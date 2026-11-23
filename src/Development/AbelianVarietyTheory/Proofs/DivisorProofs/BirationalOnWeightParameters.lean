module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem gap_add_vec {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem gaps_u₁_u₂_of_wtBig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (P : WtPar Dw) (hB : WtBig P) (τ : Psi H) (a b : Fin (Dw.p + Dw.q)) (hab : (b : ℕ) = a + 1) :
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₁ τ a - P.u₁ τ b ∧
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₂ τ a - P.u₂ τ b := by
  have hk : (a : ℕ) + 1 < Dw.p + Dw.q := by have := b.2; omega
  have g1 := hB.gaps τ a hk
  have g2 := (P.gap_rem τ a).1
  have e1 : P.u₁ τ a - P.u₁ τ b = gap (P.u₁ τ) a := (gap_eq _ hab).symm
  have e2 : P.u₂ τ a - P.u₂ τ b = gap (P.u₁ τ) a + gap (P.rem τ) a := by
    rw [← gap_eq _ hab]
    exact gap_add_vec (P.u₁ τ) (P.rem τ) a
  have hn : (CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) ≤
      (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) := by
    rw [dimFlag_eq]
    generalize FlagTan.dimFlag Dw = D
    generalize Dw.p + Dw.q = N
    generalize (D + 1).choose 2 = C
    nlinarith [Nat.zero_le (D * C), Nat.zero_le (D * N), Nat.zero_le C]
  have hn' : (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤
      (((FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) : ℕ) : ℤ) :=
    by exact_mod_cast hn
  rw [e1, e2]
  exact ⟨hn'.trans g1, by linarith⟩

end GlobalTheory.HSApp
