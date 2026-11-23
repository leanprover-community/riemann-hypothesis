module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.IsClosedImmersionLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isArithVar_mpStr (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem dim_of_isArithVar (hD : GlobalTheory.CompanionTheory.MixZ.PtDict) {m : ℕ} {n : Fin (m + 1) → ℕ} {Z : Scheme.{0}} [IsIntegral Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {d : ℕ} (hd : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) d) :
    topologicalKrullDim Z = d := by
  obtain ⟨d', hd'⟩ := (isArithVar_mpStr m n).exists_dim_eq i
  obtain ⟨-, -, h₃, -⟩ := hD m n Z i d' hd'
  have h₄ := h₃ hd.2.2.1
  have e : d' + Fintype.card (Fin (m + 1)) = d + Fintype.card (Fin (m + 1)) := by
    exact_mod_cast h₄.2.2.2.symm.trans hd.2.2.2
  rw [hd', Nat.add_right_cancel e]

end GlobalTheory.CompanionTheory.MPDict
