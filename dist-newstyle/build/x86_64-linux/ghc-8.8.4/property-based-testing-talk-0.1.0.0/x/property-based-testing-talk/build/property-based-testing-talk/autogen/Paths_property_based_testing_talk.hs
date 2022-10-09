{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_property_based_testing_talk (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/eivind/.cabal/bin"
libdir     = "/home/eivind/.cabal/lib/x86_64-linux-ghc-8.8.4/property-based-testing-talk-0.1.0.0-inplace-property-based-testing-talk"
dynlibdir  = "/home/eivind/.cabal/lib/x86_64-linux-ghc-8.8.4"
datadir    = "/home/eivind/.cabal/share/x86_64-linux-ghc-8.8.4/property-based-testing-talk-0.1.0.0"
libexecdir = "/home/eivind/.cabal/libexec/x86_64-linux-ghc-8.8.4/property-based-testing-talk-0.1.0.0"
sysconfdir = "/home/eivind/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "property_based_testing_talk_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "property_based_testing_talk_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "property_based_testing_talk_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "property_based_testing_talk_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "property_based_testing_talk_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "property_based_testing_talk_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
