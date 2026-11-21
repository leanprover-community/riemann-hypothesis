import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology

namespace HtBoundary

section Objects

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

def cuspWt (D : FullerData II Ψ K ι Ω E Em) (z : (Σ k, ι k) → ℂ) : ℝ :=
  phMu D.mu z + D.cuspU z / 2

variable (Em) in

def logDerivL : ℝ :=
  limUnder (𝓝[>] (1 : ℝ)) fun σ : ℝ =>
    (logDeriv (dedekindZeta Em) σ - logDeriv (dedekindZeta (maximalRealSubfield Em)) σ).re

variable (Em) in

def La (B : ℕ) : ℝ := Real.log (B * rootDiscr Em) + |logDerivL Em|

def Holds (Ch : ℝ) (D : FullerData II Ψ K ι Ω E Em) {M : XModel D.toComponentData}
    (S : BoundedRegularisationSetting M D.Xo D.mu.aMu (cuspWt D)) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∀ t' : ℝ, 0 < t' → t' ≤ 1 →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → ¬ OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * La Em B) - (p : ℝ) / q * D.KA ≤ htMUc D.mu S B p q t' W

end Objects

def Statement : Prop :=
  ∃ Ch : ℝ, ∀ (II : IntersectionSystem), IsIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
      (Em : Type) [Field Em] [NumberField Em] [IsCMField Em]
      (D : FullerData II Ψ K ι Ω E Em) (M : XModel D.toComponentData)
      (S : BoundedRegularisationSetting M D.Xo D.mu.aMu (cuspWt D)), S.IsTied → Holds Ch D S

namespace Flat

open GroundTheory.Heights₂.Heights.LowerBoundFree.Line GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem lineF_eq : lineF = (lineDataHodge II hII).F () := by
  show Submodule.span Ω {Pi.single 0 1} = Submodule.span Ω ((Pi.basisFun Ω (Fin 2)) '' {i | (i : ℕ) < 1})
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro rfl
    exact ⟨0, by simp, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    rw [show i = 0 from Fin.ext (Nat.lt_one_iff.mp hi)]
    simp

def flatFuller : FullerData II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) Gauss.Em where
  toComponentDataHodge := lineDataHodge II hII
  herm := Gauss.gaussDatum
  per _ _ := 1
  per_witt _ _ _ := Gauss.gauss_signature
  per_torus _ _ _ := rfl
  nStrata := 0
  stratum := Fin.elim0
  stratum_sub s := s.elim0
  stratum_cover _ h := absurd h (Set.notMem_empty _)
  stratum_torus s := s.elim0
  torLat := Fin.elim0
  torLat_le s := s.elim0
  torLat_ne s := s.elim0
  torLat_iso s := s.elim0
  torLat_sat s := s.elim0
  nz_near s := s.elim0
  mu := lineHodge II hII
  mu_F _ := lineF_eq II hII
  htLat _ _ := (lineData II hII).W ()
  ht_away _ h := absurd h (Finset.notMem_empty _)

theorem flatFuller_cuspU (z : (Σ _ : Unit, Fin 2) → ℂ) : (flatFuller II hII).cuspU z = 0 := by
  simp [FullerData.cuspU, flatFuller, Real.iSup_of_isEmpty]

def flatBReg : BoundedRegularisationSetting lineModel (flatFuller II hII).Xo (flatFuller II hII).mu.aMu
    (cuspWt (flatFuller II hII)) where
  ref := refOne
  ref_deg := rfl
  ref_smooth := refOne_smooth
  B := cpBounded
  th_ref x y _ := th_ref_line x y
  ph_eq z hz := by
    have h0 : phMu (flatFuller II hII).mu z = 0 := phMu_line (II := II) (hII := hII) (mem_mcPts_line.1 hz.2)
    show (0 : ℝ) = _
    rw [cuspWt, flatFuller_cuspU, h0, refOne_h, Real.log_one]
    ring
  ρ := (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some
  η := cpEta
  Cη := cpCutoff.choose
  cutoff := cpCutoff.choose_spec
  e1 t := t
  e1_ge _ _ := le_rfl

end Flat

end HtBoundary

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

def MUSemipositive.Statement (D : FullerData II Ψ K ι Ω E Em) {M : XModel D.toComponentData}
    (S : BoundedRegularisationSetting M D.Xo D.mu.aMu (HtBoundary.cuspWt D)) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (MUc D.mu S B p q t')

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {a : K → ℤ}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

theorem BoundedRegularisationSetting.eventually_closedBall_subset (S : BoundedRegularisationSetting M Xo a w) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.B.mid j),
      closedBall (S.B.chart j x) t ⊆ (S.B.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.B.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.B.chart j '' closure (S.B.mid j)) :=
    hc.image_of_continuousOn ((S.B.chart j).continuousOn.mono (S.B.closure_mid j))
  have hsub : S.B.chart j '' closure (S.B.mid j) ⊆ (S.B.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.B.chart j).map_source (S.B.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.B.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem BoundedRegularisationSetting.eventually_chartLevi (S : BoundedRegularisationSetting M Xo a w) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.bregWeight t) ∧
      ∀ k : Fin S.B.N, ∀ x ∈ S.B.mid k, ∀ v : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖v‖ ^ 2 ≤
          levi (S.B.chartFun (S.bregWeight t) k) (S.B.chart k x) v := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc d M.atlas S.B S.ρ S.η S.Cη t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi)

def MUcChartSemipos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (w : ((Σ k, ι k) → ℂ) → ℝ) (S : BoundedRegularisationSetting M D.Xo H.aMu w),
    ∃ c : ℝ, 0 < c ∧ ∀ (B p q : ℕ) (t δ : ℝ),
      M.atlas.Smooth (S.bregWeight t) →
      (∀ k : Fin S.B.N, ∀ x ∈ S.B.mid k, ∀ v : Fin D.n → ℂ,
        -δ * ‖v‖ ^ 2 ≤ levi (S.B.chartFun (S.bregWeight t) k) (S.B.chart k x) v) →
      (q : ℝ) * δ ≤ p * c →
      IsSemipositiveH (mCoordIdeal D.y) (MUc H S B p q t)

section Inhabitants

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {H : HodgeData D} {M : XModel D}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
end
end
