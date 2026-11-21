import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnimodF
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set Topology
open scoped Pointwise

section Abs

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem rrs_cover (μ : Measure G) [SigmaFinite μ] [μ.IsOpenPosMeasure] {V : Set G} (hV : IsOpen V) (h1 : (1 : G) ∈ V) :
    ∃ S : Set G, S.Countable ∧ ∀ y : G, ∃ x ∈ S, y ∈ x • (V * V⁻¹) := by
  classical
  obtain ⟨S, -, hSmax⟩ := zorn_subset_nonempty {S : Set G | S.PairwiseDisjoint (fun x => x • V)}
    (fun c hcS hc _ => ⟨⋃₀ c, (Set.pairwiseDisjoint_sUnion hc.directedOn).2 (fun s hs => hcS hs),
      fun s hs => Set.subset_sUnion_of_mem hs⟩) ∅ (Set.pairwiseDisjoint_empty)
  have hS : S.PairwiseDisjoint (fun x => x • V) := hSmax.prop
  refine ⟨S, ?_, ?_⟩
  · have hc := MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := μ)
      (As := fun x : S => (x : G) • V)
      (fun x => ((hV.smul (x : G)).measurableSet).nullMeasurableSet)
      (fun x y hxy => (hS x.2 y.2 (fun h => hxy (Subtype.ext h))).aedisjoint)
    have huniv : {x : S | 0 < μ ((x : G) • V)} = Set.univ :=
      Set.eq_univ_of_forall fun x => (hV.smul (x : G)).measure_pos μ ⟨(x : G) • 1, Set.smul_mem_smul_set h1⟩
    rw [huniv] at hc
    exact Set.countable_coe_iff.1 (Set.countable_univ_iff.1 hc)
  · intro y
    by_contra hcon
    push_neg at hcon
    have hyS : y ∉ S := fun hy => hcon y hy ⟨1 * 1⁻¹, Set.mul_mem_mul h1 (Set.inv_mem_inv.2 (by simpa using h1)),
      by simp⟩
    have hins : (insert y S).PairwiseDisjoint (fun x => x • V) := by
      refine hS.insert fun x hx _ => Set.disjoint_left.2 ?_
      rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
      apply hcon x hx
      refine ⟨w * v⁻¹, Set.mul_mem_mul hw (Set.inv_mem_inv.2 (by simpa using hv)), ?_⟩
      simp only [smul_eq_mul] at hvw ⊢
      rw [eq_mul_inv_of_mul_eq hvw.symm, mul_assoc]
    exact hyS (hSmax.eq_of_subset hins (Set.subset_insert y S) ▸ Set.mem_insert y S)

theorem rrs_secondCountable_abs (μ : Measure G) [SigmaFinite μ] [μ.IsOpenPosMeasure] (U : ℕ → Set G)
    (hU : ∀ n, IsOpen (U n)) (h1 : ∀ n, (1 : G) ∈ U n) (hb : ∀ O ∈ 𝓝 (1 : G), ∃ n, U n ⊆ O) :
    SecondCountableTopology G := by
  classical
  choose S hSc hS using fun n => rrs_cover μ (hU n) (h1 n)
  let B : Set (Set G) := ⋃ n, (fun x => x • (U n * (U n)⁻¹)) '' S n
  have hBc : B.Countable := Set.countable_iUnion fun n => (hSc n).image _
  refine (TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).secondCountableTopology hBc
  · intro s hs
    obtain ⟨n, x, -, rfl⟩ : ∃ n, ∃ x ∈ S n, x • (U n * (U n)⁻¹) = s := by simpa [B] using hs
    exact ((hU n).mul_right).smul x
  · intro a O haO hO
    have hO' : a⁻¹ • O ∈ 𝓝 (1 : G) :=
      (hO.smul a⁻¹).mem_nhds ⟨a, haO, by simp⟩
    obtain ⟨V₁, hV₁o, hV₁1, hV₁⟩ := exists_open_nhds_one_split hO'
    obtain ⟨V₂, hV₂o, hV₂1, hV₂⟩ := exists_open_nhds_one_split (hV₁o.mem_nhds hV₁1)
    have hW : V₂ ∩ V₂⁻¹ ∈ 𝓝 (1 : G) :=
      Filter.inter_mem (hV₂o.mem_nhds hV₂1) (hV₂o.inv.mem_nhds (by simpa using hV₂1))
    have hkey : ∀ p ∈ V₂ ∩ V₂⁻¹, ∀ q ∈ V₂ ∩ V₂⁻¹, ∀ r ∈ V₂ ∩ V₂⁻¹, ∀ s ∈ V₂ ∩ V₂⁻¹,
        a * (p * q⁻¹ * (r * s⁻¹)) ∈ O := by
      intro p hp q hq r hr s hs
      have h1' := hV₂ p hp.1 q⁻¹ (Set.mem_inv.1 hq.2)
      have h2' := hV₂ r hr.1 s⁻¹ (Set.mem_inv.1 hs.2)
      have h3 := hV₁ _ h1' _ h2'
      obtain ⟨o, ho, he⟩ := Set.mem_smul_set.1 h3
      rw [← he, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
      exact ho
    obtain ⟨n, hn⟩ := hb _ hW
    obtain ⟨x, hxS, hax⟩ := hS n a
    refine ⟨x • (U n * (U n)⁻¹), Set.mem_iUnion.2 ⟨n, x, hxS, rfl⟩, hax, ?_⟩
    obtain ⟨_, ⟨p, hp, q, hq, rfl⟩, rfl⟩ := hax
    rintro _ ⟨_, ⟨r, hr, s, hs, rfl⟩, rfl⟩
    have := hkey q⁻¹ (hn (Set.mem_inv.1 hq)) p (hn hp) r (hn hr) s⁻¹ (hn (Set.mem_inv.1 hs))
    convert this using 1
    simp only [smul_eq_mul, inv_inv]
    group

end Abs

open Formalism.MainNotions.S

theorem rr_secondCountable (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    SecondCountableTopology I.Gf := by
  obtain ⟨U, hU, h1, hb⟩ : ∃ U : ℕ → Set I.Gf, (∀ n, IsOpen (U n)) ∧ (∀ n, (1 : I.Gf) ∈ U n) ∧
      ∀ O ∈ 𝓝 (1 : I.Gf), ∃ n, U n ⊆ O := by
    refine ⟨_, fun n => I.topf_open (n + 1) (by omega), ?_, ?_⟩
    · intro n
      refine ⟨Subgroup.one_mem _, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
      simp
    · intro O hO
      obtain ⟨g, hg, hsub⟩ := I.topf_basis O hO
      refine ⟨g - 1, ?_⟩
      simp only [Nat.sub_add_cancel hg]
      exact hsub
  exact rrs_secondCountable_abs μf U hU h1 hb

end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def UnimodA (X : CData) : Prop := (X.I.muA X.μf).IsMulRightInvariant

instance rr_muG_right {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.muG ε).IsMulRightInvariant :=
  ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩

instance rr_muG_haar {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.muG ε).IsHaarMeasure := by
  unfold Formalism.REAL.muG; infer_instance

theorem rr_rep_eq_rep (I : AutInst) (fund : Set I.GA) (y : I.GA) : I.rep fund y = rr_rep I.GFset fund y := rfl

theorem rr_muA_left (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulLeftInvariant] :
    (I.muA μf).IsMulLeftInvariant :=
  Measure.prod.instIsMulLeftInvariant

theorem rr_muA_right (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulRightInvariant] :
    (I.muA μf).IsMulRightInvariant :=
  Measure.prod.instIsMulRightInvariant

theorem rr_muA_sigmaFinite (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] : SigmaFinite (I.muA μf) := by
  unfold AutInst.muA; infer_instance


theorem rr_FD_of (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (h : I.IsFundDom (I.muA μf) fund) : rr_FD (I.muA μf) (rr_GF I) fund :=
  ⟨h.1, h.2.1, h.2.2⟩

theorem rr_IsReg_of (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (h : I.IsRightReg μf fund R) :
    rr_IsReg (I.muA μf) (rr_GF I) fund R := h

def RepAlg (X : CData) : Prop :=
  (∀ g h, X.R (g * h) = X.R g ∘L X.R h) ∧ X.R 1 = 1 ∧ ∀ g (F : X.L2), ‖X.R g F‖ = ‖F‖

def RegData (X : CData) : Prop :=
  X.μf.IsHaarMeasure ∧ X.I.IsFundDom (X.I.muA X.μf) X.fund ∧ X.I.IsRightReg X.μf X.fund X.R

theorem RegData_of_HypB (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : RegData X :=
  ⟨hX.2.1.2.2.2.1, hX.2.1.2.2.2.2.1, hX.2.1.2.2.2.2.2.1⟩

theorem rightRegular_isometric_multiplicative (X : CData) (hd : RegData X) (hu : UnimodA X) : RepAlg X := by
  obtain ⟨hH, hF, hR⟩ := hd
  have := hH
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have h1 := rr_FD_of X.I X.μf X.fund hF
  have h2 := rr_IsReg_of X.I X.μf X.fund X.R hR
  exact ⟨fun g k => rr_mul h1 h2 g k, rr_one h1 h2, fun g F => rr_norm h1 h2 g F⟩

theorem regular_rep_coeff_measurable (X : CData) (hd : RegData X) (hu : UnimodA X) (x y : X.L2) :
    StronglyMeasurable fun g => ⟪x, X.R g y⟫_ℂ := by
  obtain ⟨hH, hF, hR⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  exact rr_weak_meas (rr_FD_of X.I X.μf X.fund hF) (rr_IsReg_of X.I X.μf X.fund X.R hR) x y


end Formalism.MainNotions.LeviCoordinates

end
end
