module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupSchemeStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoLBCover

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUniq

theorem mat_unique : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c c' : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c' → c = c' := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' c c' hT h₁ h₂
  obtain ⟨hAab, -, hL, hM, -, -, -, -, -, hbA, -⟩ := hH
  obtain ⟨ψA, ψB, α, hψA, hψB, hα, hrig, hmat⟩ := h₁
  obtain ⟨ψA₂, ψB₂, α₂, hψA₂, hψB₂, hα₂, hrig₂, hmat₂⟩ := h₂
  obtain rfl : ψA₂ = ψA := psi_unique _ _ (hψA₂.trans hψA.symm)
  obtain rfl : ψB₂ = ψB := psi_unique _ _ (hψB₂.trans hψB.symm)
  obtain ⟨v, hv⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.exists_ratio_gen
    (isoLB_cover (L := L) (M := M) hL hM k Φ' ψA₂ ψB₂) hα hα₂
  have v1 : v = 1 := GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one Rg A B L M k eA eB hAab hL hM R t A' B' φA' φB' Φ' ψA₂ ψB₂ α α₂ v hT hψA hψB hv hrig hrig₂
  have hαe : ∀ p, α.s p = α₂.s p := fun p => by rw [hv p, v1, map_one, _root_.one_mul]
  funext i j
  have hd := GlobalTheory.T.pullback_sections_group_scheme Rg A L k mA bA hbA R t A' φA' ψA₂ hT.1 hψA₂ (fun i => c i j - c' i j) (fun jL x hx => by
    obtain ⟨iM, hiM⟩ : ∃ iM, ((((Φ'.left ≫ ψB₂) ≫ (snd (topS Rg) B).left)).base x) ∈ M.U iM :=
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hM.cover]; trivial)
    refine ⟨(isoLB (L := L) (M := M) k Φ' ψA₂ ψB₂).U (fun _ => iM, jL), inf_le_right,
      ⟨Set.mem_iInter.2 fun _ => hiM, hx⟩, ?_⟩
    have e := (hmat j (fun _ => iM, jL)).symm.trans (hmat₂ j (fun _ => iM, jL))
    have e1 := congrArg Units.val (hαe (fun _ => iM, jL))
    erw [e1] at e
    have e2 := (α₂.s (fun _ => iM, jL)).isUnit.mul_left_cancel e
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 e2)
  exact sub_eq_zero.1 (congrFun hd i)

end GlobalTheory.HomFixUniq
