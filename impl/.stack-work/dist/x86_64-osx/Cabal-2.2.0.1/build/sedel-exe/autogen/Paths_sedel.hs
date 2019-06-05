{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_sedel (
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

bindir     = "/Users/birthevandenberg/Documents/Thesis/Git/Thesis/Implementation/impl/.stack-work/install/x86_64-osx/lts-12.16/8.4.4/bin"
libdir     = "/Users/birthevandenberg/Documents/Thesis/Git/Thesis/Implementation/impl/.stack-work/install/x86_64-osx/lts-12.16/8.4.4/lib/x86_64-osx-ghc-8.4.4/sedel-0.1.0.0-LqrmyZMzTKpE1pUwFiYG25-sedel-exe"
dynlibdir  = "/Users/birthevandenberg/Documents/Thesis/Git/Thesis/Implementation/impl/.stack-work/install/x86_64-osx/lts-12.16/8.4.4/lib/x86_64-osx-ghc-8.4.4"
datadir    = "/Users/birthevandenberg/Documents/Thesis/Git/Thesis/Implementation/impl/.stack-work/install/x86_64-osx/lts-12.16/8.4.4/share/x86_64-osx-ghc-8.4.4/sedel-0.1.0.0"
libexecdir = "/Users/birthevandenberg/Documents/Thesis/Git/Thesis/Implementation/impl/.stack-work/install/x86_64-osx/lts-12.16/8.4.4/libexec/x86_64-osx-ghc-8.4.4/sedel-0.1.0.0"
sysconfdir = "/Users/birthevandenberg/Documents/Thesis/Git/Thesis/Implementation/impl/.stack-work/install/x86_64-osx/lts-12.16/8.4.4/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "sedel_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "sedel_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "sedel_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "sedel_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "sedel_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "sedel_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
