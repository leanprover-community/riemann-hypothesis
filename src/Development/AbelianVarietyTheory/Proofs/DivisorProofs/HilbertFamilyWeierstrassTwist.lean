module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertTwistedLatticeJetsModularFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModularTransformationLevelStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam

theorem famGL_coe_redGL (N : ℕ) (γ : SL(2, ℤ)) :
    ((redGL N γ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) := rfl

theorem famGL_vmul_gact (N : ℕ) (y : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) (γ : SL(2, ℤ)) :
    vmul y (gact N 1 α γ) = vact N (vmul y α) γ := by
  rw [gact_one, vact, vmul, vmul, vmul, Matrix.vecMul_vecMul, Units.val_mul]

theorem isFam_hfun_GL : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (y : Fin 2 → ZMod N) (κ : Emb F → ℕ), IsFam (gact N 1) (wt (2 * s) κ : ℕ) (fun α ↦ hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hF s N _ L hs hL y κ
  refine GlobalTheory.T.hilbertTwistedLattice_jets_modular_family hE F hF s N L hs (Nat.pos_of_ne_zero (NeZero.ne N)) hL (GL (Fin 2) (ZMod N)) (gact N 1)
    (fun α ↦ (α : Matrix (Fin 2) (Fin 2) (ZMod N))) (fun α ↦ wB N (vmul y α)) κ ?_ ?_
  · intro α γ
    simp only [gact_one, Units.val_mul, famGL_coe_redGL]
  · intro α γ τ
    simp only [famGL_vmul_gact]
    exact GlobalTheory.T.weierstrass_modular_transformation_level N (vmul y α) γ τ

end GlobalTheory.HilbFam
