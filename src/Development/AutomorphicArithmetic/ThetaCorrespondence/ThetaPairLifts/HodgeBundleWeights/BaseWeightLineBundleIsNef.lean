import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadWeightLineNef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadWeightLineNefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailWeightLineNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailWeightLineNefStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleUnitWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGapStatement

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefHodge
section Step
open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM)
open GlobalTheory.QCoh (pullbackSections)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z C : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (g : C ⟶ Z) (σ : E →+* ℂ)
  (f : ∀ M : MChart Y, Fin M.n → Γ(Lie Y.t.G, M.U))
end Step
theorem isNef_hodgeBundle_headWeight : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  intro hS _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk
  rw [NefStep.L₀_headWt TF.X Z τ k hk]
  exact isNef_stepEx hS hN.1 TF.X Z τ.1 (by rw [FlagMod.mult_of_mem τ]; exact hk)
end GlobalTheory.NefHodge
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_headWeight_nef : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  first | exact @_root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight | exact _root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight | (intros; apply _root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight <;> assumption)
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefStep
theorem isNef_hodgeBundle_tailWeight : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  intro h _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk _
  letI := algebraΓOfHom (str₀ TF.X Z)
  rw [L₀_tailWt TF.X Z τ k hk]
  have hq := FlagMod.mult_conj (Dw := Dw) τ
  exact isNef_pull_LL_stepEx TF.X.F h hN.1 c.F (inc₀ TF.X Z) _ (by omega)
end GlobalTheory.NefStep
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_tailWeight_nef : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  first | exact @_root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight | exact _root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight | (intros; apply _root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight <;> assumption)
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefWt
theorem weight_line_bundle_isNef : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ la : AllWt.Weight Dw, GapGe 0 la → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z la) := by
  intro hPr hNN hSA E _ _ _ H Dw l Xo c TF Z hF la hla
  letI := algebraΓOfHom (str₀ TF.X Z)
  classical
  obtain ⟨-, hproj, -⟩ := GlobalTheory.T.flagSpace_component_smooth_projective_connected E H Dw l Xo c TF Z hF
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hproj
  let C := common₀ TF.X Z
  let φ := AddMonoidHom.mk' (fun a => cls (L₀ TF.X Z a) (C.isLB a)) (cls_common_add C)
  have hφ : ∀ a, cls (L₀ TF.X Z a) (C.isLB a) = φ a := fun _ => rfl
  have nef0 : ∀ a, φ a = 0 → IsNef c.F (L₀ TF.X Z a) := fun a h =>
    (isNef_triv c.F _).of_cls_eq (C.isLB a) (by rw [hφ, h]; rfl)
  by_cases hN : 0 < Dw.p + Dw.q
  swap
  · refine nef0 la ?_
    have : la = 0 := funext fun τ => funext fun i => absurd i.2 (by omega)
    rw [this, map_zero]
  have key : la = _ := decomp la hla hN
  let cτ : Psi H → ℤ := fun τ => la τ ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ) k else 0
  let W : (Psi H × ℕ) ⊕ (Psi H × Bool) → AllWt.Weight Dw := Sum.elim (fun y : Psi H × ℕ => piece Dw y.1 y.2)
    (fun y : Psi H × Bool => unitWt y.1 (if y.2 then 1 else -1))
  have hP : ∀ x, IsNef c.F (L₀ TF.X Z (W x)) := by
    rintro (⟨τ, k⟩ | ⟨τ, b⟩)
    · show IsNef c.F (L₀ TF.X Z (piece Dw τ k))
      unfold piece
      split_ifs with h1 h2
      · exact _root_.GlobalTheory.T.hodgeBundle_headWeight_nef hSA hPr hNN E H Dw l Xo c TF Z hF τ k h2
      · exact _root_.GlobalTheory.T.hodgeBundle_tailWeight_nef hSA hPr hNN E H Dw l Xo c TF Z hF τ k (not_lt.1 h2) h1
      · exact nef0 0 (map_zero φ)
    · cases b
      · exact (_root_.GlobalTheory.T.hodgeBundle_unitWeight_nef hPr hNN E H Dw l Xo c TF Z hF τ).2
      · exact (_root_.GlobalTheory.T.hodgeBundle_unitWeight_nef hPr hNN E H Dw l Xo c TF Z hF τ).1
  refine IsNef.of_cls_eq_sum ((Finset.univ ×ˢ Finset.range (Dw.p + Dw.q - 1)).disjSum Finset.univ) hP
    (Sum.elim (fun y : Psi H × ℕ => (gap (la y.1) y.2).toNat)
      (fun y : Psi H × Bool => if y.2 then (cτ y.1).toNat else (-cτ y.1).toNat)) hA (C.isLB la) ?_
  rw [hφ]
  conv_lhs => rw [key]
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_nsmul]
  rcases x with ⟨τ, k⟩ | ⟨τ, b⟩ <;> rfl
end GlobalTheory.NefWt
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_weight_line_bundle_is_nef : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ la : AllWt.Weight Dw, GapGe 0 la → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z la) := by
  first | exact @_root_.GlobalTheory.NefWt.weight_line_bundle_isNef | exact _root_.GlobalTheory.NefWt.weight_line_bundle_isNef | (intros; apply _root_.GlobalTheory.NefWt.weight_line_bundle_isNef <;> assumption)
end
end
