import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StStokesLimitFam
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarChartSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarChartSemiposFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D), ∃ c : ℝ, 0 < c ∧
    ∀ (B p q : ℕ) (t δ : ℝ),
      X.M.atlas.Smooth (X.S.regWeight t) →
      (∀ k : Fin X.S.R.N, ∀ x ∈ X.S.R.mid k, ∀ w : Fin D.n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k x) w) →
      (q : ℝ) * δ ≤ p * c →
      IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}

omit [DecidableEq Ψ] in

theorem NbarChartSemiposFam.hyps_of_setting (X : ComponentFamilySetting D) {c : ℝ} (hc : 0 < c) :
    ∃ t δ : ℝ, 0 < t ∧ X.M.atlas.Smooth (X.S.regWeight t) ∧
      (∀ k : Fin X.S.R.N, ∀ x ∈ X.S.R.mid k, ∀ w : Fin D.n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k x) w) ∧
      ((1 : ℕ) : ℝ) * δ ≤ ((1 : ℕ) : ℝ) * c := by
  have hlim : Tendsto (fun t => 4 * X.S.Cη * X.S.e1 t) (𝓝[>] 0) (𝓝 0) := by
    simpa using X.S_tied.e1_tendsto_zero.const_mul (4 * X.S.Cη)
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
  have hev := (X.S.eventually_chartLevi X.S_tied).and (h1.and (hlim.eventually (eventually_le_nhds hc)))
  obtain ⟨t, ⟨hs, hl⟩, ht, hδ⟩ := hev.exists
  exact ⟨t, 4 * X.S.Cη * X.S.e1 t, ht, hs, hl, by simpa using hδ⟩

namespace Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem NbarChartSemiposFam.hyps_inhabited {c : ℝ} (hc : 0 < c) :
    ∃ t δ : ℝ, 0 < t ∧ (projLineFamilySetting II hII).M.atlas.Smooth ((projLineFamilySetting II hII).S.regWeight t) ∧
      (∀ k : Fin (projLineFamilySetting II hII).S.R.N, ∀ x ∈ (projLineFamilySetting II hII).S.R.mid k,
        ∀ w : Fin (LowerBoundFree.Line.lineData II hII).n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi ((projLineFamilySetting II hII).S.R.chartFun ((projLineFamilySetting II hII).S.regWeight t) k)
          ((projLineFamilySetting II hII).S.R.chart k x) w) ∧
      ((1 : ℕ) : ℝ) * δ ≤ ((1 : ℕ) : ℝ) * c :=
  NbarChartSemiposFam.hyps_of_setting _ hc

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarLeviChartFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w →
    ∀ k : Fin X.S.R.N, X.M.proj z ∈ X.S.R.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v ∧
        levi (fun y => Real.log ((X.NbarQ B p q t).h y)) z w =
          q * levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k (X.M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z w

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}

namespace Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem NbarLeviChartFam.hyps_inhabited :
    ∃ t : ℝ, 0 < t ∧ (projLineFamilySetting II hII).M.atlas.Smooth ((projLineFamilySetting II hII).S.regWeight t) ∧
    LowerBoundFree.Line.discL 0 ∈ mcPts (mCoordIdeal (LowerBoundFree.Line.lineData II hII).y) ∧
    IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (LowerBoundFree.Line.lineData II hII).y)
      (LowerBoundFree.Line.discL 0) LowerBoundFree.Line.velL ∧
    ∃ k : Fin (projLineFamilySetting II hII).S.R.N,
      (projLineFamilySetting II hII).M.proj (LowerBoundFree.Line.discL 0) ∈ (projLineFamilySetting II hII).S.R.mid k := by
  obtain ⟨t, -, ht, hs, -⟩ := NineStatements.NbarChartSemiposFam.hyps_of_setting (projLineFamilySetting II hII) one_pos
  exact ⟨t, ht, hs, LowerBoundFree.Line.discL_mem 0, LowerBoundFree.Line.isConeTangent_velL, (0 : Fin 2),
    LowerBoundFree.Line.projL_discL_mem_mid⟩

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}

def regNbarQ (H : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B p q : ℕ) (t : ℝ) :
    HermLine ι :=
  smoothRep (mCoordIdeal D.y)
    (hermOfFun ι ((q : ℤ) • muTwDeg H B + (p : ℤ) • D.a') fun z =>
      (S.ref.h z * Real.exp (S.regWeight t (M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p)

def NbarLeviChartReg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (S : LogLogRegularisationSetting M D.Xo (muLine H)), S.IsTied → ∀ (B p q : ℕ) (t : ℝ),
    M.atlas.Smooth (S.regWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w →
    ∀ k : Fin S.R.N, M.proj z ∈ S.R.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel M (S.R.chart k) z w v ∧
        levi (fun y => Real.log ((regNbarQ H M S B p q t).h y)) z w =
          q * levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k (M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z w

theorem NbarLeviChart.of_reg (h : NbarLeviChartReg.Statement) : LowerBoundFree.NbarLeviChart.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q t hs z hz w hw k hk
  exact h II Ψ K ι Ω E D X.H X.M X.S X.S_tied B p q t hs z hz w hw k hk

namespace Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem NbarLeviChartReg.hyps_inhabited :
    (projLineFamilySetting II hII).S.IsTied ∧
    ∃ t : ℝ, 0 < t ∧ (projLineFamilySetting II hII).M.atlas.Smooth ((projLineFamilySetting II hII).S.regWeight t) ∧
    LowerBoundFree.Line.discL 0 ∈ mcPts (mCoordIdeal (LowerBoundFree.Line.lineData II hII).y) ∧
    IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (LowerBoundFree.Line.lineData II hII).y)
      (LowerBoundFree.Line.discL 0) LowerBoundFree.Line.velL ∧
    ∃ k : Fin (projLineFamilySetting II hII).S.R.N,
      (projLineFamilySetting II hII).M.proj (LowerBoundFree.Line.discL 0) ∈ (projLineFamilySetting II hII).S.R.mid k :=
  ⟨(projLineFamilySetting II hII).S_tied, NbarLeviChartFam.hyps_inhabited II hII⟩

end Line

end GroundTheory.Heights₂.Heights.NineStatements
end
end
