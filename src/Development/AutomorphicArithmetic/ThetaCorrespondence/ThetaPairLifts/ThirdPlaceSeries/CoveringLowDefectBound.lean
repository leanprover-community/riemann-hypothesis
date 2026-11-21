import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringLowDefectBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefectBoundOfConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDimensionLogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDimensionLogBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN

section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovTop.DefSizes
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.DefSizes
namespace GlobalTheory.CovTop.DefSizes
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.DefSizes
namespace GlobalTheory.CovTop.DefSizes
theorem parameters_scale_rank_gap_bounds :
    _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → |(ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| *
      (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) -
        (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) τ : ℝ)|) +
      (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) +
      ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd (Fm.D x ι).host.E| ≤
      C * unitE p := by
  have hdim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ w : ℤ,
      (GlobalTheory.DualWeyl.dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := fun n la h => (GlobalTheory.T.dualWeyl_dim_formula_duality_bound n la h).2.2
  have H := Closed.and _root_.GlobalTheory.CovTop.WtShape.wtN_z (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1)
  simp only [_root_.GlobalTheory.CovTop.LiftWeightNumerator, _root_.GlobalTheory.CovTop.HostNAlt, _root_.GlobalTheory.CovTop.LiftsCondition] at H
  unfold _root_.GlobalTheory.CovTop.LiftsCondition
  refine Closed.imp H ?_
  intro eps Fm CH _ h
  obtain ⟨⟨C1, -, hw⟩, ⟨A, -, hh⟩⟩ := h
  obtain ⟨x0, h⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hw hh
  exact ⟨35, by norm_num, x0, fun x hx hle ι p hp i _ =>
    sizes_at p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i) (Fm.sizes x hx ι) hdim⟩
end GlobalTheory.CovTop.DefSizes
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_dimension_log_bound' : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → |(ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| * (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) - (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) τ : ℝ)|) + (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) + ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd (Fm.D x ι).host.E| ≤ C * unitE p := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.DefLow
theorem covering_low_defect_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.LowDefectCondition := by
  intro hP hG hA
  have hc := _root_.GlobalTheory.T.two_mul_defBound_sub_le_muCore_of_gramAt hP
  refine Closed.imp ((hA.and (hG.and (_root_.GlobalTheory.CovTop.WtShape.wtN_z.and _root_.GlobalTheory.T.weight_dimension_log_bound'))).and hc) fun Fm CH _ h => ?_
  obtain ⟨⟨⟨CA, hCA, xA, eA⟩, ⟨CG, -, xG, eG⟩, ⟨CW, -, xW, eW⟩, ⟨C3, hC3, x3, e3⟩⟩, ⟨C₀, hC₀, x0, h1⟩⟩ := h
  refine ⟨CA + C3 + C₀, by positivity, max (max (max xA xG) (max xW x3)) x0,
    fun x hx hle' ι p hp i hi => ?_⟩
  have hle := le_trans (le_max_left _ _) hle'
  have l0 : x0 ≤ x := le_trans (le_max_right _ _) hle'
  have lA : xA ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have lG : xG ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have lW : xW ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have l3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle
  have a := eA x hx lA ι p hp i
  have g := eG x hx lG ι p hp i
  have w := eW x hx lW ι p hp i
  have s := e3 x hx l3 ι p hp i hi
  have c := h1 x hx l0 ι p hp i hi g
  have hk := (Fm.D x ι).R.m_add_three_le_k
  have q0 : (dat p i).q = 0 := by
    rw [w.sig.2.1]; unfold Ranks.sigW; simp only; omega
  have p1 : 1 ≤ (dat p i).p := by
    rw [w.sig.1]; unfold Ranks.sigW; simp only; omega
  have ar := GlobalTheory.T.two_definiteBound_ge_anchoredMainTerm_sub_crude_errors _ _ (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1)
    (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm q0 p1 (p.κ i).n_even
  have a1 := a.1
  simp only [q0, Nat.cast_zero, sub_zero] at a1
  rw [abs_le] at a1
  unfold LowAt
  linarith [a1.1, a1.2]
end GlobalTheory.CovTop.DefLow
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowDef_of_gram_of_anchor : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.LowDefectCondition := by
  first | exact @_root_.GlobalTheory.CovTop.DefLow.covering_low_defect_alt | exact _root_.GlobalTheory.CovTop.DefLow.covering_low_defect_alt | (intros; apply _root_.GlobalTheory.CovTop.DefLow.covering_low_defect_alt <;> assumption)
end
end
end
