module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrInternal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem part_indep {O X R : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R]
    (W : WPres O X R) : iSupIndep W.part := by
  have h := (W.A.val.toLinearMap.iSupIndep_map Subtype.val_injective
    (gr_internal O X R W).submodule_iSupIndep)
  convert h using 1
  funext j
  rw [WPres.gr, Submodule.map_comap_eq, eq_comm, inf_eq_right]
  intro x hx
  exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩

private theorem part_gen {O X R : Type} [CommRing O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [CommRing R] [Algebra O R] (W : WPres O X R) :
    Algebra.adjoin O ((W.part 0 : Set R) ∪ Set.range W.z) = W.A := by
  have h := congrArg (Subalgebra.map W.A.val) (gr_gen O R X W)
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val] at h
  rw [← h]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    constructor
    · intro hx
      exact ⟨⟨x, W.part_le_A hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · ext x
    simp [WPres.zA, WPres.z]

private theorem quot_pres {O X R S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing S] [Algebra O S] [IsCO O S] (W : WPres O X R) (org : W.HasOrigin) (π : R →ₐ[O] S)
    (surj : Function.Surjective π) {κ : Type} [Finite κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i))
    (ker : RingHom.ker π = Ideal.span (Set.range g)) :
    ∃ WS : WPres O X S, (∀ w, WS.part w = (W.part w).map π.toLinearMap) ∧ ∀ i, WS.z i ∈ maximalIdeal S := by
  have hz : ∀ i, W.z i ∈ maximalIdeal R := by
    intro i
    let ψ : R →+* ResidueField O := (IsLocalRing.residue O).comp (W.origin org).toRingHom
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨algebraMap O R a, by simp [ψ]⟩
    have heq : RingHom.ker ψ = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
    rw [← heq, RingHom.mem_ker]
    simp [ψ, WPres.z, WPres.origin_π]
  have hhom : IsHomog O W.wt (RingHom.ker (π.comp W.π)) := by
    have h := (homog_span O R X W κ (fun i => ⟨g i, W.part_le_A (hg i)⟩) c
      (fun i => Submodule.mem_comap.mpr (hg i))).1
    convert h using 1
    ext f
    rw [RingHom.mem_ker, Ideal.mem_comap]
    show π (W.π f) = 0 ↔ W.π f ∈ Ideal.span (Set.range g)
    rw [← ker, RingHom.mem_ker]
  refine ⟨W.quot π surj hhom, ?_, ?_⟩
  · intro w
    exact Submodule.map_comp W.π.toLinearMap π.toLinearMap (wtPart O W.wt w)
  · intro i
    show π (W.z i) ∈ maximalIdeal S
    rw [← res_eq_zero_iff O S, res_map, res_eq_zero_iff]
    exact hz i

theorem UpperTheory.V.GradeZeroInterpolatingElement.sInternal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, iSupIndep M.sPart ∧ (∃ s : Finset M.S, (∀ x ∈ s, ∃ w, x ∈ M.sPart w) ∧ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ s) = M.SS) ∧ ∃ WS : WPres c.O (ℤ × ℤ) M.S, (∀ w, WS.part w = M.sPart w) ∧ ∀ i, WS.z i ∈ maximalIdeal M.S := by
  intro Ω _ _ _ l _ c D _ M
  classical
  let g : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → M.R := Sum.elim M.F (Sum.elim M.E M.Z)
  let cw : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → ℤ × ℤ :=
    Sum.elim (fun _ => -wPs) (Sum.elim (fun _ => wPs) (fun _ => 0))
  have hg : ∀ i, g i ∈ M.W.part (cw i) := by
    rintro (i | i | i)
    · exact M.hF i
    · exact M.hE i
    · exact (M.hZ i).1
  have hker : RingHom.ker M.π = Ideal.span (Set.range g) := by
    rw [M.ker]
    simp only [g, Set.Sum.elim_range, Set.union_assoc]
  obtain ⟨WS, hpart, hzm⟩ := quot_pres M.W M.org M.π M.surj g cw hg hker
  have hp : WS.part = M.sPart := funext hpart
  have hA : WS.A = M.SS := by
    unfold WPres.A Model.SS
    congr
  haveI := WS.fin
  refine ⟨by rw [← hp]; exact part_indep WS, ⟨Finset.univ.image WS.z, ?_, ?_⟩, WS, hpart, hzm⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨WS.wt i, by rw [← hp]; exact WS.z_mem i⟩
  · rw [← hA, ← part_gen WS, ← hp]
    congr 2
    simp
