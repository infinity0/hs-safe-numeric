{-# LANGUAGE CPP #-}
import           Test.DocTest

main :: IO ()
#if __GLASGOW_HASKELL__ >= 800
-- GHC before this version doesn't support MIN_VERSION_*
-- so doctest doesn't work since it runs outside of cabal
main = doctest ["-i", "src"]
#else
main = return ()
#endif
