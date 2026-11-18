-- | checked dependent core. source expressions enter through
-- 'Tung.Source'; raw evaluation and scoped checking remain private.
module Tung.Core
  ( Level (..),
    Constraint (..),
    Plicity (..),
    Term (..),
    HostLiteral (..),
    children,
    mapChildren,
    SymbolId (..),
    ModuleId (..),
    inductionSymbol,
    Environment,
    emptyEnvironment,
    Inferred (..),
    infer,
    check,
    define,
    validate,
    normalise,
    InductiveDeclaration (..),
    defineInductive,
    defineInductives,
    inferInductive,
    inferInductives,
    universeNormalise,
    universeSatisfiable,
    universeEntails,
  )
where

import Tung.Core.Check
import Tung.Core.Inductive
import Tung.Core.Syntax (HostLiteral (..), children, mapChildren)
import Tung.Identity (inductionSymbol)
