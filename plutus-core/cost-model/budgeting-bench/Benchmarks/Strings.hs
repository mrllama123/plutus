{- | Benchmarks for string builtins.  Remember that "strings" are actually Text. -}

module Benchmarks.Strings (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore                             as PLC
import           PlutusCore.Evaluation.Machine.ExMemory

import           Criterion.Main
import           Data.ByteString                        as BS
import           Data.Functor                           ((<&>))
import qualified Data.Text                              as T
import qualified Data.Text.Encoding                     as T
import           System.Random                          (StdGen)

import qualified Hedgehog                               as H
import qualified Hedgehog.Internal.Gen                  as G
import qualified Hedgehog.Range                         as R

import qualified Debug.Trace                            as T

{- The memory usage of a string is defined to be four bytes per character.  Plutus
 strings are implemented as Text objects, which are UTF-16 encoded sequences of
 Unicode characters.  For characters (by which Text means codepoints) in the
 Basic Multilingual Plane, UTF-16 requires two bytes, and for other planes four
 bytes (and the actual codepoint for these is obtained by extracting certain
 bits from the two 16-bit parts of the encoding).  The characters we'll
 encounter in practice will probably all be in the BMP (perhaps with the
 exception of emoji), but we still allow one word per character, the number of
 characters being given by 'Data.Text.length'.  For benchmarking it's not
 entirely clear what sort of strings we should provide as input: strings of
 two-byte characters or strings of four-byte characters.  Four-byte characters
 may require some extra processing by certain functions, so we use those as
 input in order to get worst-case behaviour.  This may overestimate costs for
 the strings we encounter in practice.
-}

{- | Note [Unicode encodings and Data.Text] Unicode characters are organised into
17 'planes', each containing 65536 'codepoints'.  Only some of the codepoints in
each plane represent actual characters: some code pointsare permanently
unavailable, some are used for non-printing operations like forming ligatures or
adding accents, and some are used for other administrative purposes.  To
complicate matters, an actual rendered character (grapheme) may be constructed
from multiple codepoints, but that shouldn't concern us here.

Plane 0 is called the Basic Multilingual Plane (BMP) and contains most commonly
used characters from most human languages.

Plutus Strings are implemented as Text objects, which are UTF-16 encoded
sequences of Unicode characters (Text refers to characters, but really means
codepoints).  In UTF-16, characters in the BMP are encoded using two bytes, and
characters from other planes require four bytes (encoded using 'surrogate'
codepoints in the ranges 0xD800-0xDBFF and 0xDC00-0xDFFF, the actual character
being encoded using the lower-order bits).  Text strings internally contain an
Array of 16-byte values, but the length reported by Data.Text.length s is the
number of Unicode characters.  Thus a Text string containing n characters will
require between 2*n and 4*n bytes of memory, the latter case occurring when
every character in s lies outside the BMP (Data.Text.Foreign.lengthWord16 tells
you the number of 16-bit words in the internal representation). Calculating the
character length of a Text string requires traversal of the entire string, so is
O(n).

We provide builtins for the encodeUtf8 and decodeUtf8 functions, which convert
Text objects to UTF-8 encoded Strings and back.  UTF-8 uses 1 to four bytes for
each character: ASCII characters (0x00-0x7F) require one byte, 1920 characters
in various common scripts (Latin-1, Cyrillic, ...) require two bytes, three bytes
are required for everything else in the BMP, and four bytes for codepoints from
the other planes.

In practice we'll probably mostly encounter ASCII strings (which are cheap to
process and encode), but for costing purposes we have to consider the most
expensive operations.  Thus we benchmark 'encodeUtf8' with inputs produced by
Hedgehog's 'unicode' generator, which produces characters uniformly distributed
over the entire set of planes.  Typically, over 9% of the characters generated
by this require four bytes in UTF-8 (and two in UTF-16).  If we use the 'ascii'
generator instead then a Text string of length n requires exactly n bytes,
and if we use 'latin1' then about 3n/2 bytes are required (the characters
in 0x00-0x7F need one byte in UTF-8, those in 0x80-0xFF require two, so the
average number of bytes per character is 3/2).
-}


seedA :: H.Seed
seedA = H.Seed 42 43

seedB :: H.Seed
seedB = H.Seed 44 45

oneArgumentSizes :: [Integer]
oneArgumentSizes = [0, 100..10000] -- 101 entries

twoArgumentSizes :: [Integer]
twoArgumentSizes = [0, 250..5000]  -- 21 entries


{- This makes a Text string containing n unicode characters.  We use the unicode
 generator since that mostly produces 4 bytes per character, which is the worst
 case. If we were to use the ascii generator that would give us two bytes per
 character. -}
makeSizedTextString :: H.Seed -> Int -> T.Text
makeSizedTextString seed n = genSample seed (G.text (R.singleton n) G.unicode)

makeSizedTextStrings :: H.Seed -> [Integer] -> [T.Text]
makeSizedTextStrings seed sizes = fmap (makeSizedTextString seed . fromInteger) sizes

benchOneTextString :: DefaultFun -> Benchmark
benchOneTextString name =
    createOneTermBuiltinBench name $ makeSizedTextStrings seedA oneArgumentSizes


{- | Generate a valid UTF-8 bytestring with memory usage approximately n for
benchmarking decodeUtf8.  The 'utf8' generator produces bytestrings containing n
UTF-8 encoded Unicode characters, and if we use the 'unicode' generator most of
these will require four bytes, so the output will have memory usage of
approximately n words.  If we used 'ascii' instead then we'd get exactly n
bytes, so n/4 words. We want to measure the worst-case time of decoding a
bytestring 'b' of length n, and it's not initially clear when the worst case
occurs.  If 'b' contains only ascii characters then 'decodeUtf8' will have to
process n characters, but processing each character will be cheap; if 'b'
contains only characters outside the BMP then there will be n/4 characters but
each one will be expensive to process.  Benchmarking shows that the latter is
about x times more expensive than the former, so we use the latter here.
-}
makeSizedUtf8ByteString :: H.Seed -> Int -> BS.ByteString
makeSizedUtf8ByteString seed n = genSample seed (G.utf8 (R.singleton n) G.unicode)

makeSizedUtf8ByteStrings :: H.Seed -> [Integer] -> [BS.ByteString]
makeSizedUtf8ByteStrings seed sizes = (makeSizedUtf8ByteString seed . fromInteger) <$> sizes

{- This is for DecodeUtf8.  That fails if the encoded data is invalid, so we make
   sure that the input data is valid data for it by using data produced by
   G.utf8 (see above). -}
benchOneUtf8ByteString :: DefaultFun -> Benchmark
benchOneUtf8ByteString name =
    createOneTermBuiltinBench name $ makeSizedUtf8ByteStrings seedA oneArgumentSizes

benchTwoTextStrings :: DefaultFun -> Benchmark
benchTwoTextStrings name =
    let s1 = makeSizedTextStrings seedA twoArgumentSizes
        s2 = makeSizedTextStrings seedB twoArgumentSizes
    in createTwoTermBuiltinBench name s1 s2

benchTextStringNoArgOperations :: DefaultFun -> Benchmark
benchTextStringNoArgOperations name =
    bgroup (show name) $
        fmap (\x -> benchDefault (showMemoryUsage x) $ mkApp1 name x) oneArgumentSizes

-- Copy the bytestring here, because otherwise it'll be exactly the same, and the equality will short-circuit.
benchSameTwoTextStrings :: DefaultFun -> Benchmark
benchSameTwoTextStrings name = createTwoTermBuiltinBenchElementwise name inputs (fmap T.copy inputs)
                               where inputs = makeSizedTextStrings seedA oneArgumentSizes

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = [ benchOneTextString EncodeUtf8
                      , benchOneUtf8ByteString DecodeUtf8
                      , benchTwoTextStrings AppendString
                      , benchSameTwoTextStrings EqualsString
                      ]


