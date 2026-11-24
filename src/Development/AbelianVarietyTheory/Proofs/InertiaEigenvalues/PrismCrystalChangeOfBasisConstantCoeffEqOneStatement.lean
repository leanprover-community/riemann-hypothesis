module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCrystalChangeOfBasisConstantCoeffEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (κ₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, κ₀ τ (δ.f y) = PowerSeries.constantCoeff (κ τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)).map PowerSeries.constantCoeff = 1 := by
  first | exact @GlobalTheory.CrysDiag.eps_constantCoeff_eq_one | exact GlobalTheory.CrysDiag.eps_constantCoeff_eq_one | (intros; apply GlobalTheory.CrysDiag.eps_constantCoeff_eq_one <;> assumption)
