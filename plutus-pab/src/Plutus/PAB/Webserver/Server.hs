{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Plutus.PAB.Webserver.Server
    ( startServer
    , startServer'
    , startServerDebug
    , startServerDebug'
    ) where

import           Cardano.Wallet.Types            (WalletInfo (..))
import           Control.Concurrent              (MVar, forkFinally, forkIO, newEmptyMVar, putMVar)
import           Control.Concurrent.Availability (Availability, available, newToken)
import qualified Control.Concurrent.STM          as STM
import           Control.Monad                   (void, when)
import           Control.Monad.Except            (ExceptT (ExceptT))
import           Control.Monad.Freer.Extras.Log  (logInfo, logWarn)
import           Control.Monad.IO.Class          (liftIO)
import           Data.Aeson                      (FromJSON, ToJSON)
import           Data.Bifunctor                  (first)
import qualified Data.ByteString.Lazy.Char8      as LBS
import           Data.Function                   ((&))
import           Data.Monoid                     (Endo (..))
import           Data.Proxy                      (Proxy (Proxy))
import           Ledger.Crypto                   (pubKeyHash)
import           Network.Wai                     (Middleware)
import qualified Network.Wai.Handler.Warp        as Warp
import           Network.Wai.Middleware.Cors     (simpleCors)
import           Plutus.PAB.Core                 (PABAction, PABRunner (..))
import qualified Plutus.PAB.Core                 as Core
import qualified Plutus.PAB.Effects.Contract     as Contract
import qualified Plutus.PAB.Monitoring.PABLogMsg as LM
import           Plutus.PAB.Simulator            (Simulation)
import qualified Plutus.PAB.Simulator            as Simulator
import           Plutus.PAB.Types                (PABError, WebserverConfig (..), baseUrl, defaultWebServerConfig)
import           Plutus.PAB.Webserver.API        (API, WSAPI, WalletProxy)
import           Plutus.PAB.Webserver.Handler    (apiHandler, walletProxy, walletProxyClientEnv)
import qualified Plutus.PAB.Webserver.WebSocket  as WS
import           Servant                         (Application, Handler (Handler), Raw, ServerT, err500, errBody,
                                                  hoistServer, serve, serveDirectoryFileServer, (:<|>) ((:<|>)))
import qualified Servant
import           Servant.Client                  (BaseUrl (baseUrlPort), ClientEnv)
import           Wallet.Emulator.Wallet          (WalletId)

asHandler :: forall t env a. PABRunner t env -> PABAction t env a -> Handler a
asHandler PABRunner{runPABAction} = Servant.Handler . ExceptT . fmap (first mapError) . runPABAction where
    mapError :: PABError -> Servant.ServerError
    mapError e = Servant.err500 { Servant.errBody = LBS.pack $ show e }

type CombinedAPI t =
      API (Contract.ContractDef t) WalletId
      :<|> WSAPI

app ::
    forall t env.
    ( FromJSON (Contract.ContractDef t)
    , ToJSON (Contract.ContractDef t)
    , Contract.PABContract t
    , Servant.MimeUnrender Servant.JSON (Contract.ContractDef t)
    ) =>
    Maybe FilePath
    -> Either ClientEnv (PABAction t env WalletInfo) -- ^ wallet client (if wallet proxy is enabled)
    -> PABRunner t env
    -> Application
app fp walletClient pabRunner = do
    let apiServer :: ServerT (CombinedAPI t) Handler
        apiServer =
            Servant.hoistServer
                (Proxy @(CombinedAPI t))
                (asHandler pabRunner)
                (apiHandler :<|> WS.wsHandler)

    case fp of
        Nothing -> do
            let wp = either walletProxyClientEnv walletProxy walletClient
                rest = Proxy @(CombinedAPI t :<|> (WalletProxy WalletId))
                wpServer =
                    Servant.hoistServer
                        (Proxy @(WalletProxy WalletId))
                        (asHandler pabRunner)
                        wp
            Servant.serve rest (apiServer :<|> wpServer)
        Just filePath -> do
            let wp = either walletProxyClientEnv walletProxy walletClient
                wpServer =
                    Servant.hoistServer
                        (Proxy @(WalletProxy WalletId))
                        (asHandler pabRunner)
                        wp
                fileServer :: ServerT Raw Handler
                fileServer = serveDirectoryFileServer filePath
                rest = Proxy @(CombinedAPI t :<|> (WalletProxy WalletId) :<|> Raw)
            Servant.serve rest (apiServer :<|> wpServer :<|> fileServer)


-- | Start the server using the config. Returns an action that shuts it down
--   again, and an MVar that is filled when the webserver
--   thread exits.
startServer ::
    forall t env.
    ( FromJSON (Contract.ContractDef t)
    , ToJSON (Contract.ContractDef t)
    , Contract.PABContract t
    , Servant.MimeUnrender Servant.JSON (Contract.ContractDef t)
    )
    => WebserverConfig -- ^ Optional file path for static assets
    -> Either ClientEnv (PABAction t env WalletInfo)
    -> Availability
    -> PABAction t env (MVar (), PABAction t env ())
startServer WebserverConfig{baseUrl, staticDir, permissiveCorsPolicy, endpointTimeout} walletClient availability = do
    when permissiveCorsPolicy $
      logWarn @(LM.PABMultiAgentMsg t) (LM.UserLog "Warning: Using a very permissive CORS policy! *Any* website serving JavaScript can interact with these endpoints.")
    startServer' [mw] (baseUrlPort baseUrl) walletClient staticDir availability (timeout endpointTimeout)
      where
        mw = if permissiveCorsPolicy then simpleCors else id
        -- By default we use the normal request timeout: 30 seconds. But if
        -- someone has asked for a longer endpoint timeout, we need to set
        -- that to be the webserver timeout as well.
        timeout Nothing  = 30
        timeout (Just s) = fromIntegral $ max s 30

-- | Start the server. Returns an action that shuts it down
--   again, and an MVar that is filled when the webserver
--   thread exits.
startServer' ::
    forall t env.
    ( FromJSON (Contract.ContractDef t)
    , ToJSON (Contract.ContractDef t)
    , Contract.PABContract t
    , Servant.MimeUnrender Servant.JSON (Contract.ContractDef t)
    )
    => [Middleware] -- ^ Optional wai middleware
    -> Int -- ^ Port
    -> Either ClientEnv (PABAction t env WalletInfo) -- ^ How to generate a new wallet, either by proxying the request to the wallet API, or by running the PAB action
    -> Maybe FilePath -- ^ Optional file path for static assets
    -> Availability
    -> Int
    -> PABAction t env (MVar (), PABAction t env ())
startServer' waiMiddlewares port walletClient staticPath availability timeout = do
    simRunner <- Core.pabRunner
    shutdownVar <- liftIO $ STM.atomically $ STM.newEmptyTMVar @()
    mvar <- liftIO newEmptyMVar

    let shutdownHandler :: IO () -> IO ()
        shutdownHandler doShutdown = void $ forkIO $ do
            STM.atomically $ STM.takeTMVar shutdownVar
            putStrLn "webserver: shutting down"
            doShutdown
        warpSettings :: Warp.Settings
        warpSettings = Warp.defaultSettings
            & Warp.setPort port
            & Warp.setInstallShutdownHandler shutdownHandler
            & Warp.setBeforeMainLoop (available availability)
            & Warp.setTimeout timeout
        middleware = appEndo $ foldMap Endo waiMiddlewares
    logInfo @(LM.PABMultiAgentMsg t) (LM.StartingPABBackendServer port)
    void $ liftIO $
        forkFinally
            (Warp.runSettings warpSettings $ middleware
               $ app staticPath walletClient simRunner)
            (\_ -> putMVar mvar ())

    pure (mvar, liftIO $ STM.atomically $ STM.putTMVar shutdownVar ())

-- | Start the server using a default configuration for debugging.
startServerDebug ::
    ( FromJSON (Contract.ContractDef t)
    , ToJSON (Contract.ContractDef t)
    , Contract.PABContract t
    , Servant.MimeUnrender Servant.JSON (Contract.ContractDef t)
    )
    => Simulation t (Simulation t ())
startServerDebug = startServerDebug' defaultWebServerConfig

-- | Start the server using (mostly) a default configuration for debugging,
-- but allow an optional webserver config.
startServerDebug' ::
    ( FromJSON (Contract.ContractDef t)
    , ToJSON (Contract.ContractDef t)
    , Contract.PABContract t
    , Servant.MimeUnrender Servant.JSON (Contract.ContractDef t)
    )
    => WebserverConfig
    -> Simulation t (Simulation t ())
startServerDebug' conf = do
    tk <- newToken
    let mkWalletInfo = do
            (wllt, pk) <- Simulator.addWallet
            pure $ WalletInfo{wiWallet = wllt, wiPubKey = pk, wiPubKeyHash = pubKeyHash pk}
    snd <$> startServer conf (Right mkWalletInfo) tk
