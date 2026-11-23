module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

section
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothLev_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) :
    Q.SmoothLev k r 0 Set.univ (fun y => ∑ i ∈ t, c i • f i y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Formalism.FourierDecayAlt.P.Qx2.smooth_zero
  | insert a t ha ih =>
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', he⟩ := ih g₀ hg₀
    obtain ⟨V, h', hV, hgV, hh', he'⟩ := hf a g₀ hg₀
    refine ⟨U ∩ V, fun y => c a • h' y + f' y, hU.inter hV, ⟨hgU, hgV⟩,
      ((hh'.mono Set.inter_subset_right).const_smul (c a)).add (hf'.mono Set.inter_subset_left), ?_⟩
    intro g hg hgG
    beta_reduce
    rw [Finset.sum_insert ha, he' g hg.2 hgG, ← he g hg.1 hgG]

theorem capelli_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) (Y : ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Q.CV k r Y (fun y => ∑ i ∈ t, c i • f i y) g = ∑ i ∈ t, c i • Q.CV k r Y (f i) g := by
  classical
  have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := E) Y
  have hg' := Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg
  induction t using Finset.induction_on with
  | empty => simpa using hT.map_zero hg'
  | insert a t ha ih =>
    have h := hT.lin _ (f a) (c a) (smoothLev_finsum_smul t c f hf) (hf a) g hg'
    simp only [Finset.sum_insert ha]
    rw [← ih, add_comm, ← h]
    congr 1
    funext y
    rw [add_comm]

end

theorem foldr_capelli_sum_eigen : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ev : Fin N₀ → ℝ → ℂ) (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) → (∀ i (Y : ℝ), ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ev i Y • Fi i g) → (∀ g ∈ B.GV k r, F g = ∑ i, Fi i g) → ∀ w : List (Bool × ℝ), ∀ g ∈ B.GV k r, (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) g = ∑ i, (w.map fun a => s * ev i a.2).prod • Fi i g := by
  intro k r Wp Wq _ _ _ _ _ _ N₀ Fi ev s F hs hev hF w
  induction w with
  | nil => intro g hg; simpa using hF g hg
  | cons a w ih =>
    intro g hg
    have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := Wq →L[ℂ] Wp) (a.2 : ℂ)
    have h1 := hT.loc _ _ (fun y hy => ih y hy.1.1) g (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg)
    have h2 := capelli_finsum_smul Finset.univ (fun i => (w.map fun a => s * ev i a.2).prod) Fi
      (fun i => Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck (hs i)) (a.2 : ℂ) hg
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, Pi.smul_apply]
    rw [h1.trans h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i a.2 g hg, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory
