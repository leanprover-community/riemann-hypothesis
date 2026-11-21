import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

namespace GlobalTheory.ReadingIndependence

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Theta Formalism.BasicNotions.TH

theorem jInjRd_of_laws {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : JInjRd T j a n := by
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  refine jInjRd_of_wt T hM hj a n (fun p y ψ => ?_)
    (GlobalTheory.Frames.algebraic_laws hS _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.1
  exact GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ _ _ _ (T.Q.Xo j) T.Q.c _ _ ψ y

theorem sum_toLp_ae {α : Type} [MeasurableSpace α] (μ : Measure α) {m : ℕ} (φ : Fin m → α → ℂ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (g : Fin m → ℂ) (s : Finset (Fin m)) :
    ((∑ i ∈ s, g i • (hφ i).toLp (φ i) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] ∑ i ∈ s, g i • φ i := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact Lp.coeFn_zero ℂ 2 μ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.add ?_ ih)
    exact (Lp.coeFn_smul _ _).trans (((hφ i).coeFn_toLp).const_smul (g i))

section General

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] {σ : K →+* ℂ}
  {X : Comp → Data E r} (V : HSp D) (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
  (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu)

theorem sum_ae {m : ℕ} (b : Fin m → C) (g : Fin m → ℂ) :
    ((∑ i, g i • uniformisationL2 V σ rd dict mu h (b i) : Lp ℂ 2 (muQ1 V)) : AutQ V → ℂ) =ᵐ[muQ1 V]
      onQ V (adel V dict mu (∑ i, g i • rd (b i))) := by
  have e : onQ V (adel V dict mu (∑ i, g i • rd (b i))) = ∑ i, g i • jFn V σ rd dict mu (b i) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul]
    rfl
  rw [e]
  exact sum_toLp_ae (muQ1 V) (fun i => jFn V σ rd dict mu (b i)) (fun i => h (b i)) g Finset.univ


end General





end GlobalTheory.ReadingIndependence
