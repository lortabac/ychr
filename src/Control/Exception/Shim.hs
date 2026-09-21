-- |
-- Module      : Control.Exception.Shim
-- Description : 'Control.Exception.try' with GHC's type-variable order.
--
-- MicroHs declares @try :: forall a e. Exception e => IO a -> IO (Either e a)@
-- (@MicroHs\/lib\/Control\/Exception.hs@), while GHC's @base@ orders the
-- variables the other way (@forall e a@). Both compilers honour the
-- /declared/ order for a visible type application, so @try \@SomeException@
-- selects @e@ under GHC and @a@ under MicroHs. This module re-exports
-- "Control.Exception" with 'try' replaced by a version whose explicit
-- @forall e a@ gives GHC's order on both compilers; a call site can then
-- keep its @try \@T@ unchanged.
--
-- Only 'try' is adjusted. The other "Control.Exception" functions either
-- agree with GHC's order when type-applied ('catch', 'handle', 'tryJust')
-- or are never type-applied in YCHR ('bracket', 'finally', 'onException',
-- 'throwIO' — all four order their variables differently under MicroHs;
-- see @dev-docs\/MICROHS_GAPS.md@, gap 7).
--
-- Import this module instead of "Control.Exception" wherever @try@ is
-- imported. Delete it (and revert the importers) once MicroHs orders
-- @try@ the way @base@ does.
module Control.Exception.Shim
  ( module Control.Exception,
    try,
  )
where

import Control.Exception hiding (try)
import Control.Exception qualified as E

-- | 'Control.Exception.try' with GHC's type-variable order.
--
-- The explicit @forall e a@ is the point: it is what makes
-- @try \@SomeException@ select the exception type on both compilers.
-- Had the signature been left implicit, MicroHs would infer its own order
-- and select the result type.
try :: forall e a. (Exception e) => IO a -> IO (Either e a)
try = E.try
