module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemOfLpCharLpSpEqSumList
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyFreeSumIrreducibles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
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
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace GlobalTheory.VWeil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_pow_frob_comm (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ, Commute (ρ σ) (ρ (frob h) ^ m) := by
  classical
  have h1 : ∀ T : Set.range fun τ : Ine (F := E) A => ρ (ineIncl h τ),
      ∃ m : ℕ, 0 < m ∧ Commute T.1 (ρ (frob h) ^ m) := by
    rintro ⟨_, τ, rfl⟩
    obtain ⟨m, hm, hpow⟩ := exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ
      (ineIncl h τ * frob h * (ineIncl h τ)⁻¹) (frob h) (by simp)
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, conj_pow] at hpow
    show ρ (ineIncl h τ) * _ = _ * ρ (ineIncl h τ)
    conv_rhs => rw [← hpow]
    rw [← map_pow, ← map_mul, ← map_mul, inv_mul_cancel_right]
  choose m hm hc using h1
  haveI := hρ.finite_range.fintype
  refine ⟨∏ T, m T, Finset.prod_pos fun T _ => hm T, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  rw [hτ, map_mul]
  refine Commute.mul_left ?_ ?_
  · rw [← map_pow]
    exact ((Commute.refl (frob h)).zpow_left _).pow_right _ |>.map ρ
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ ⟨_, τ, rfl⟩)
    rw [hk, pow_mul]
    exact (hc ⟨_, τ, rfl⟩).pow_right k

theorem isSemisimple_apply (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) (σ : Weil h) : End.IsSemisimple (ρ σ) := by
  classical
  obtain ⟨m, hm, hc⟩ := exists_pow_frob_comm ρ hρ
  refine isSemisimple_of_isSemisimple_frob E Ω A w h V ρ hρ (frob h) deg_frob
    (FrobSemisimple.isSemisimple_of_pow ((Group.isUnit _).map ρ) hm ?_) σ
  set T := ρ (frob h) ^ m with hT
  let p : ℂ[X] := ∏ μ ∈ (minpoly ℂ T).roots.toFinset, (X - C μ)
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := p)
    (Separable.squarefree (separable_prod_X_sub_C_iff'.2 fun _ _ _ _ e => e)) ?_
  have hcp : ∀ g, Commute (ρ g) (aeval T p) := fun g => by
    simp only [p, map_prod]
    rw [aeval_eq_sum_range]
    exact Commute.sum_right _ _ _ fun i _ => ((hc g).pow_right i).smul_right _
  let K : Subrepresentation ρ := ⟨LinearMap.ker (aeval T p), fun g v hv => by
    rw [LinearMap.mem_ker, ← End.mul_apply, ← (hcp g).eq, End.mul_apply, LinearMap.mem_ker.1 hv,
      map_zero]⟩
  obtain ⟨Q, hQ⟩ := hss.exists_isCompl K
  have hinf : K.toSubmodule ⊓ Q.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hQ.inf_eq_bot
  have hsup : K.toSubmodule ⊔ Q.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hQ.sup_eq_top
  have hQT : ∀ v ∈ Q.toSubmodule, T v ∈ Q.toSubmodule := fun v hv => by
    rw [hT, ← map_pow]; exact Q.apply_mem_toSubmodule _ hv
  have hQ0 : Q.toSubmodule = ⊥ := by
    by_contra hne
    haveI : Nontrivial Q.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := End.exists_eigenvalue (T.restrict hQT)
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv1 : T v = μ • (v : V) := congrArg Subtype.val hv.apply_eq_smul
    have hv0 : (v : V) ≠ 0 := fun e => hv.2 (Subtype.ext e)
    have hvT : End.HasEigenvector T μ v := ⟨End.mem_eigenspace_iff.2 hv1, hv0⟩
    have hroot : μ ∈ (minpoly ℂ T).roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots (minpoly.ne_zero_of_finite ℂ T)]
      exact End.hasEigenvalue_iff_isRoot.1 (End.hasEigenvalue_of_hasEigenvector hvT)
    have hK : (v : V) ∈ K.toSubmodule := by
      show aeval T p v = 0
      rw [End.aeval_apply_of_hasEigenvector hvT, show p.eval μ = 0 from ?_, zero_smul]
      simp only [p, eval_prod]
      exact Finset.prod_eq_zero hroot (by simp)
    exact hv0 ((Submodule.mem_bot ℂ).1 (hinf ▸ Submodule.mem_inf.2 ⟨hK, v.2⟩))
  rw [hQ0, sup_bot_eq] at hsup
  exact LinearMap.ker_eq_top.1 hsup

def wdOfRep (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) : WDRep h V where
  ρ := ρ
  N := 0
  smooth := hρ
  semisimple := isSemisimple_apply ρ hρ hss
  nilpotent := IsNilpotent.zero
  comm σ := by simp


variable (h) in
abbrev IrrW : Type := {x : WD h // IsIrrWD x}

theorem isIrrWD_mk (a : WDRep h V) : IsIrrWD (WD.mk a) ↔ a.ρ.IsIrreducible := by
  constructor
  · rintro ⟨n, b, hb, hirr⟩
    obtain ⟨e, he, -⟩ := WD.mk_eq_mk.1 hb
    exact IrrDecomp.isIrreducible_of_equiv e he hirr
  · intro hirr
    obtain ⟨e, he, -⟩ := WD.iso_std a
    exact ⟨_, (WD.std a).2, (WD.sound (WD.iso_std _)).symm, IrrDecomp.isIrreducible_of_equiv e he hirr⟩

theorem nontrivial_of_irr {ρ : Representation ℂ (Weil h) V} (hρ : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem N_eq_zero_of_irr (a : WDRep h V) (hirr : a.ρ.IsIrreducible) : a.N = 0 := by
  apply GlobalTheory.WeilDeligne.SpSummand.N_eq_zero_of_irr <;> assumption

theorem IrrW.mono0 (z : IrrW h) : z.1.mono0 := by
  obtain ⟨_, n, a, rfl, ha⟩ := z
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff a).2 (N_eq_zero_of_irr a ha)

theorem IrrW.lpDim_pos (z : IrrW h) : 0 < z.1.lpDim := by
  obtain ⟨_, n, a, rfl, ha⟩ := z
  have := nontrivial_of_irr ha
  show 0 < (WD.mk a).lpDim
  rw [WD.lpDim_mk]
  exact finrank_pos

theorem isIrrWD_lpOfChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : IsIrrWD (WD.lpOfChar h χ hχ) := by
  refine ⟨1, _, rfl, ?_⟩
  haveI : IsSimpleModule ℂ (Fin 1 → ℂ) := isSimpleModule_iff_finrank_eq_one.2 (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · exact bot_ne_top (α := Submodule ℂ (Fin 1 → ℂ)) (congrArg Subrepresentation.toSubmodule hbt)
  · rcases eq_bot_or_eq_top U.toSubmodule with hU | hU
    · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
    · exact Or.inr (Subrepresentation.toSubmodule_injective hU)

def IrrW.ofChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : IrrW h :=
  ⟨WD.lpOfChar h χ hχ, isIrrWD_lpOfChar χ hχ⟩


variable (h) in
def frobCoset (r : ℕ) : Set (Weil h) := {τ | deg τ = -(r : ℤ)}

@[simp] theorem mem_frobCoset {r : ℕ} {τ : Weil h} : τ ∈ frobCoset h r ↔ deg τ = -(r : ℤ) := Iff.rfl




section Artin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Artin


variable (h) in
abbrev VR : Type := IrrW h →₀ ℚ

namespace VR






end VR

end GlobalTheory.VWeil
