module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafPullConnectingCompatStatement
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Nt2

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison.Om.Cech

theorem top_le_map {X Y : TopCat.{0}} (f : X ⟶ Y) : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤ := le_top

theorem zeroEquiv_eq_equivZero {X : TopCat.{0}} (F : AbSheaf X) (W : Opens X) (x : Sheaf.H'.{0} F 0 W) :
    GlobalTheory.SiteCoh.zeroEquiv F W x = GlobalTheory.SheafLES.equivZero.{0} F W x :=
  rfl

-- Keep the sheafification instances abstract until the final specialization to opens.
private theorem sitePull_zero_terminal {C D : Type} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{0}] [HasSheafify K AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf J AddCommGrpCat.{0})] [HasExt.{0} (Sheaf K AddCommGrpCat.{0})]
    (p : C ⥤ D) [p.IsContinuous J K]
    [PreservesFiniteLimits (p.sheafPullback AddCommGrpCat.{0} J K)]
    {F : Sheaf J AddCommGrpCat.{0}} {G : Sheaf K AddCommGrpCat.{0}}
    (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{0} J K).obj G)
    {V : C} {W : D} (hV : IsTerminal V) (hW : IsTerminal W) (i : W ⟶ p.obj V)
    (s : F.obj.obj (op V)) :
    GlobalTheory.SiteCoh.terminalEquiv G 0 hW
        (sitePull p φ 0 i ((GlobalTheory.SiteCoh.terminalEquiv F 0 hV).symm
          ((Sheaf.H.equiv₀ F hV).symm s))) =
      (Sheaf.H.equiv₀ G hW).symm (G.obj.map i.op (φ.hom.app (op V) s)) := by
  let e := Sheaf.H.equiv₀ F hV
  let e' := Sheaf.H.equiv₀ G hW
  let t := GlobalTheory.SiteCoh.terminalEquiv F 0 hV
  let x := t.symm (e.symm s)
  let y := sitePull p φ 0 i x
  have hx : GlobalTheory.SheafLES.equivZero F V x = s :=
    (GlobalTheory.SiteCoh.equiv₀_terminalEquiv F hV x).symm.trans
      ((congrArg (fun z => e z) (t.apply_symm_apply (e.symm s))).trans (e.apply_symm_apply s))
  apply e'.eq_symm_apply.mpr
  exact (GlobalTheory.SiteCoh.equiv₀_terminalEquiv G hW y).trans
    ((equivZero_sitePull p φ i x).trans (congrArg (fun z => G.obj.map i.op (φ.hom.app (op V) z)) hx))

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G')
    (s : G.obj.obj (op ⊤)) :
    hPull f φ 0 ((Sheaf.H.equiv₀ G isTerminalTop).symm s) =
      (Sheaf.H.equiv₀ G' isTerminalTop).symm (GroundTheory.Arith.SchemeCoh.res G'.obj (top_le_map f) (φ.hom.app (op ⊤) s)) := by
  exact sitePull_zero_terminal (Opens.map f) (F := G) (G := G') φ
    isTerminalTop isTerminalTop (homOfLE (top_le_map f)) s

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q) {κ ι : Type} (V : κ → Opens Y)
    (U : ι → Opens X) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (GroundTheory.Arith.SchemeCoh.res Q (top_le_map f) (φ.app (op ⊤) s))).1 := by
  funext j
  change GroundTheory.Arith.SchemeCoh.res Q _ (φ.app _ (GroundTheory.Arith.SchemeCoh.res P _ s)) =
    GroundTheory.Arith.SchemeCoh.res Q _ (GroundTheory.Arith.SchemeCoh.res Q _ (φ.app (op ⊤) s))
  rw [app_res_map, GroundTheory.Arith.SchemeCoh.res_res, GroundTheory.Arith.SchemeCoh.res_res]

theorem cechHZeroEquiv_mk {X : TopCat.{0}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) {ι : Type} (U : ι → Opens X)
    (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P) (hU : iSup U = ⊤) (s : P.obj (op ⊤)) :
    cechHZeroEquiv P U hP hU (QuotientAddGroup.mk (globalCocycle P U s)) = s := by
  change (globalCocycleEquiv P U hP hU).symm (globalCocycle P U s) = s
  exact (globalCocycleEquiv P U hP hU).symm_apply_apply s

private theorem pull_eq_of_sections {A A' B B' C C' : Type}
    (q : A → B) (q' : A' → B') (r : A → A') (p : B → B') (p' : C → C')
    (e : B → C) (e' : B' → C') (d : A → C) (d' : A' → C')
    (hq : Function.Surjective q) (hp : ∀ s, p (q s) = q' (r s))
    (he : ∀ s, e (q s) = d s) (he' : ∀ s, e' (q' s) = d' s)
    (hd : ∀ s, p' (d s) = d' (r s)) (x : B) : e' (p x) = p' (e x) := by
  obtain ⟨s, rfl⟩ := hq x
  calc
    e' (p (q s)) = e' (q' (r s)) := congrArg e' (hp s)
    _ = d' (r s) := he' (r s)
    _ = p' (d s) := (hd s).symm
    _ = p' (e (q s)) := congrArg p' (he s).symm

private theorem cechPullH_globalCocycle_mk {X Y : TopCat.{0}} (f : X ⟶ Y)
    {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    (φ : P ⟶ (Opens.map f).op ⋙ Q) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    cechPullH f φ V U τ hτ 0 (QuotientAddGroup.mk (globalCocycle P V s)) =
      QuotientAddGroup.mk (globalCocycle Q U (res Q (top_le_map f) (φ.app (op ⊤) s))) :=
  congrArg (QuotientAddGroup.mk : cocycles Q U 0 → cechH Q U 0)
    (Subtype.ext (pullCoch_globalCocycle f φ V U τ hτ s))

private theorem pull_eq_of_equiv {A A' B B' C C' : Type}
    [Add A] [Add A'] [Add B] [Add B'] [Add C] [Add C']
    (e : B ≃+ A) (e' : B' ≃+ A') (d : A ≃+ C) (d' : A' ≃+ C')
    (r : A → A') (p : B → B') (p' : C → C')
    (hp : ∀ s, p (e.symm s) = e'.symm (r s)) (hd : ∀ s, p' (d s) = d' (r s)) (x : B) :
    (e'.trans d') (p x) = p' ((e.trans d) x) :=
  pull_eq_of_sections e.symm e'.symm r p p' (e.trans d) (e'.trans d') d d'
    e.symm.surjective hp (fun s => congrArg d (e.apply_symm_apply s))
    (fun s => congrArg d' (e'.apply_symm_apply s)) hd x

theorem cechHZero_pull' : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G') (x : cechH G.obj V 0),
    (cechHZeroEquivH G' U hU : cechH G'.obj U 0 ≃+ Sheaf.H.{0} G' 0) (cechPullH f φ.hom V U τ hτ 0 x) =
      hPull f φ 0 ((cechHZeroEquivH G V hV : cechH G.obj V 0 ≃+ Sheaf.H.{0} G 0) x) := by
  intro X Y f κ ι V hV U hU τ hτ G G' φ x
  let ψ : G.obj ⟶ (Opens.map f).op ⋙ G'.obj := φ.hom
  let e := cechHZeroEquiv G.obj V G.property hV
  let e' := cechHZeroEquiv G'.obj U G'.property hU
  let p := cechPullH f ψ V U τ hτ 0
  let r (s : G.obj.obj (op ⊤)) := res G'.obj (top_le_map f) (ψ.app (op ⊤) s)
  have hp (s : G.obj.obj (op ⊤)) : p (e.symm s) = e'.symm (r s) := by
    have hs := e.symm_apply_eq.mpr (cechHZeroEquiv_mk G.obj V G.property hV s).symm
    have hs' := e'.symm_apply_eq.mpr (cechHZeroEquiv_mk G'.obj U G'.property hU (r s)).symm
    exact (congrArg (fun z => p z) hs).trans ((cechPullH_globalCocycle_mk f ψ V U τ hτ s).trans hs'.symm)
  exact pull_eq_of_equiv e e' (Sheaf.H.equiv₀ G isTerminalTop).symm
    (Sheaf.H.equiv₀ G' isTerminalTop).symm r p (hPull f φ 0) hp (hPull_zero f (G' := G') φ) x

theorem cechHOne_pull' : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : cechH S.X₁.obj V 1),
    (cechHOneEquiv U hU hS' hC' hI' : cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  intro X Y f κ ι V hV U hU τ hτ S S' hS _ hC hI hS' _ hC' hI' α x
  let φ₁ : S.X₁.obj ⟶ (Opens.map f).op ⋙ S'.X₁.obj := α.τ₁.hom
  let φ₂ : S.X₂.obj ⟶ (Opens.map f).op ⋙ S'.X₂.obj := α.τ₂.hom
  let φ₃ : S.X₃.obj ⟶ (Opens.map f).op ⋙ S'.X₃.obj := α.τ₃.hom
  have h₁₂ : ∀ (W : (Opens Y)ᵒᵖ) (z : S.X₁.obj.obj W),
      φ₂.app W (S.f.hom.app W z) = S'.f.hom.app _ (φ₁.app W z) :=
    fun W z => congrArg (fun g : S.X₁ ⟶ (S'.map (push f)).X₂ => g.hom.app W z) α.comm₁₂.symm
  have h₂₃ : ∀ (W : (Opens Y)ᵒᵖ) (z : S.X₂.obj.obj W),
      φ₃.app W (S.g.hom.app W z) = S'.g.hom.app _ (φ₂.app W z) :=
    fun W z => congrArg (fun g : S.X₂ ⟶ (S'.map (push f)).X₃ => g.hom.app W z) α.comm₂₃.symm
  let r (s : S.X₃.obj.obj (op ⊤)) := res S'.X₃.obj (top_le_map f) (φ₃.app (op ⊤) s)
  have hL (s : S.X₃.obj.obj (op ⊤)) :
      cechPullH f φ₁ V U τ hτ 1 (cechOneProj V hC s) = cechOneProj U hC' (r s) :=
    (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' φ₁ φ₂ φ₃ h₁₂ h₂₃ 0
      (globalCocycle S.X₃.obj V s)).trans
      (congrArg (fun z => hC'.delta 0 z) (Subtype.ext (pullCoch_globalCocycle f φ₃ V U τ hτ s)))
  have hδ (s : S.X₃.obj.obj (op ⊤)) :
      hPull f α.τ₁ 1 (hOneProj hS s) = hOneProj hS' (r s) :=
    (GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α 0 ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s)).trans
      (congrArg (fun z => H.δ hS' 0 (0 + 1) rfl z) (hPull_zero f (G' := S'.X₃) α.τ₃ s))
  exact pull_eq_of_sections (cechOneProj V hC) (cechOneProj U hC') r
    (cechPullH f φ₁ V U τ hτ 1) (hPull f α.τ₁ 1)
    (cechHOneEquiv V hV hS hC hI) (cechHOneEquiv U hU hS' hC' hI')
    (hOneProj hS) (hOneProj hS') (cechOneProj_surjective V hV hC hI) hL
    (cechHOneEquiv_cechOneProj V hV hS hC hI) (cechHOneEquiv_cechOneProj U hU hS' hC' hI') hδ x

end CrystallineSemistableComparison.Om.Nt2
