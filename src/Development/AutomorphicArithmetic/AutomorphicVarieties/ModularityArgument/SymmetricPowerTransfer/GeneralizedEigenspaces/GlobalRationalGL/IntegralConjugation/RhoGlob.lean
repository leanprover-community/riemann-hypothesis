module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoGlob :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v w h (x : Lsq (Lp L) P.Δ), P.rho v w h (lmap (cv v) P.Δ x) = algebraMap L (Kw w) (P.e x) := by
  intro L _ _ _ P v w h x
  have hx : x = algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.re
      + algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.im * QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
  have lhs : P.rho v w h (lmap (cv v) P.Δ x)
      = P.φ v w h (cv v x.re) + P.φ v w h (cv v x.im) * P.rt w := rfl
  rw [lhs, P.φ_alg, P.φ_alg, Pre.rt]
  conv_rhs => rw [hx]
  rw [map_add (f := _), map_mul, P.e_alg, P.e_alg, map_add (f := _), map_mul]
