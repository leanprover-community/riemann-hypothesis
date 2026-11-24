module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem le_v_of_norm_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (k : ℕ)
    (hx : ‖x‖ ≤ (l : ℝ) ^ (-(k : ℤ))) :
    ((k : ℚ) : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlk : (l : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero k hl
  have hy : ‖x / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow, div_le_one (zpow_pos hlpos _)]
    exact hx
  obtain ⟨y, hxy⟩ : ∃ y : ℤ_[l], x = (l : ℚ_[l]) ^ k * (y : ℚ_[l]) := by
    refine ⟨⟨x / (l : ℚ_[l]) ^ k, hy⟩, ?_⟩
    show x = (l : ℚ_[l]) ^ k * (x / (l : ℚ_[l]) ^ k)
    field_simp
  have hmem : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) ∈ OL LL := by
    have e : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) = algebraMap ℤ_[l] ↥LL.1 y := rfl
    rw [e]
    exact (OL LL).algebraMap_mem y
  have hv0 : 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l])) := (P.27 LL _).2 hmem
  have hk : k • (1 : WithTop ℚ) = ((k : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_one]
  rw [hxy, map_mul, map_pow, map_natCast, (P.v LL).map_mul, (P.v LL).map_pow, P.26 LL, hk]
  exact le_add_of_nonneg_right hv0

theorem grp_GKs_H : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  intro l _ P _ K s LL _ W hW g
  have hcyc : IsCyc P.χQ := P.20
  have hχ : ((P.PD K).χ g : ℚ_[l]) = (P.χQ (g : GQ l) : ℚ_[l]) := P.PD_χ K g
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · unfold Gj at hg
    obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) s
    have hmem : ζ ∈ Ks K s := by
      unfold Ks
      exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ _)
        (IntermediateField.subset_adjoin ℚ_[l] _ hζ.pow_eq_one)
    have hfix : (g : GQ l) ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have hn : ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) :=
      hcyc.norm_sub_one_le_of_prim (g : GQ l) s hζ hfix
    have hv := le_v_of_norm_le P LL ((P.χQ (g : GQ l) : ℚ_[l]) - 1) s hn
    have e : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) - 1 =
        algebraMap ℚ_[l] ↥LL.1 ((P.χQ (g : GQ l) : ℚ_[l]) - 1) := by
      rw [hχ, map_sub, map_one]
    rw [W.GKs_def g, hW, e]
    exact_mod_cast hv
  · unfold Hinf at hg
    have hall : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      intro m
      refine (hcyc.fix_iff (g : GQ l) m).1 (fun ζ hζ => ?_)
      have hmem : ζ ∈ Kinf K := by
        unfold Kinf
        exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | ∃ j : ℕ, x ^ l ^ j = 1} ≤ _)
          (IntermediateField.subset_adjoin ℚ_[l] _ ⟨m, hζ⟩)
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      by_contra hne
      have hpos : 0 < ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hpos
      exact absurd (hall m) (not_le.2 hm)
    have h2 : (algebraMap ↥(OL LL) ↥LL.1) ↑(W.χΓ (W.resΓ g)) = 1 := by
      rw [W.χΓ_res g, hχ, h1, map_one]
    have h3 : ((W.χΓ (W.resΓ g) : ↥(OL LL))) = 1 := Subtype.ext h2
    have h4 : W.χΓ (W.resΓ g) = 1 := Units.val_eq_one.1 h3
    exact W.χΓ_inj (by rw [h4, map_one])

end GlobalTheory.Cyc.Decomp
