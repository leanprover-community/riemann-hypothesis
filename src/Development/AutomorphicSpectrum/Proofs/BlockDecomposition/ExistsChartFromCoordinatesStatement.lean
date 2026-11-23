module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CompanionTheory.ChartAlg in

theorem _root_.GlobalTheory.T.exists_chart_from_coordinates : ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ)
    (hb : TFBase γ l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)
    (hκ : ∀ a, κ a = Ideal.Quotient.mk I (algebraMap O R a)) {V : X.Opens} {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∃ (c' : Chart γ 0 q κ V d) (e : R ⊗[O] Γ(X, V) ≃+* c'.D.B), TF l s c'.D ∧ (∀ r, e (r ⊗ₜ 1) = c'.D.i r) ∧
      (∀ i, e (1 ⊗ₜ c.t i) = c'.t i) ∧ ∀ f, ev c'.D c'.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f)) := by
  intro O R _ _ _ I γ l s hb X q κ hκ V d c
  let a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  have hstr : algebraMap O Γ(X, V) = strV q V := rfl
  have hE : (MvPolynomial.eval₂Hom (algebraMap O Γ(X, V)) c.t : MvPolynomial (Fin d) O →+* Γ(X, V)).Etale := c.etale
  have hF : Module.Flat O Γ(X, V) := flat_of_etale c.t hE
  let iL : R →+* R ⊗[O] Γ(X, V) := Algebra.TensorProduct.includeLeftRingHom
  have hl : ∀ x : R ⊗[O] Γ(X, V), (l : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun x h => by
    have := tf_tensor (G := Γ(X, V)) (O := O) (pdP γ s) l (hb.tf s) x (by rw [h]; exact zero_mem _)
    rw [hb.nil, Ideal.map_bot] at this
    exact this
  have hlk : ∀ (k : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) ^ k * x = 0 → x = 0 := fun k => by
    induction k with
    | zero => intro x h; simpa using h
    | succ k ih =>
      intro x h
      refine ih x (hl _ ?_)
      rw [← h, pow_succ']
      ring
  have hn : ∀ n : ℕ, n ≠ 0 → ∀ x : R ⊗[O] Γ(X, V), (n : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun n hn0 x h => by
    obtain ⟨k, u, hu⟩ := hb.dv n hn0
    refine hlk k x ?_
    have e := congrArg iL hu
    rw [map_mul, map_pow, map_natCast, map_natCast] at e
    rw [← e, mul_comm (n : R ⊗[O] Γ(X, V)), mul_assoc, h, mul_zero]
  obtain ⟨δ, hδ⟩ := exists_dp γ iL hn
  have hP := dividedPowerFiltration_eq_map γ iL δ hδ
  let g : Γ(X, V) →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL :=
    (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[O] R ⊗[O] Γ(X, V)).toRingHom
  let ψ : R ⧸ I →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL := Ideal.quotientMap _ iL Ideal.le_comap_map
  have hcomp : g.comp (strV q V) = ψ.comp κ := RingHom.ext fun a => by
    change Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[O] (algebraMap O Γ(X, V) a)) = ψ (κ a)
    rw [hκ]
    change _ = Ideal.Quotient.mk _ ((algebraMap O R a) ⊗ₜ[O] (1 : Γ(X, V)))
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let y : PtOver X q κ ((R ⊗[O] Γ(X, V)) ⧸ I.map iL) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec), by
      change (Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec) ≫ q = _
      rw [Category.assoc, fromSpec_comp q c.affine, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]⟩
  have hnil : IsNilpotent (I.map iL) := ⟨s, by
    have h := pow_le_pdP δ s
    rw [hP, hb.nil, Ideal.map_bot] at h
    exact le_bot_iff.1 h⟩
  let D : Thick (nlFun γ 0 X q κ) := mkT (R ⊗[O] Γ(X, V)) iL (I.map iL) δ ⟨fun h => (h rfl).elim, fun _ => hnil⟩ hδ y
    (fun r => rfl)
  have hin : InU V D := top_le_specMap c.affine g
  let c' : Chart γ 0 q κ V d :=
    { D := D
      t := fun k => (1 : R) ⊗ₜ[O] c.t k
      etale := etale_tensor c.t hE
      J_eq := rfl
      inV := hin
      rep := fun B' y' hy' => rep_tensor hstr hκ c.affine y (fun r => rfl) g (fun f => rfl) rfl B' y' hy' }
  have key : ∀ (r : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) * x ∈ pdP δ r → x ∈ pdP δ r := fun r x hx => by
    rw [hP] at hx ⊢
    exact tf_tensor (pdP γ r) l (hb.tf r) x hx
  refine ⟨c', RingEquiv.refl _, ⟨?_, fun r x hx => ?_⟩, fun r => rfl, fun k => rfl, fun f => ?_⟩
  · change pdP δ s = ⊥
    rw [hP, hb.nil, Ideal.map_bot]
  · exact key r x hx
  · have := evalAt_specMap c.affine g (pt D) rfl hin
    exact RingHom.congr_fun this f
