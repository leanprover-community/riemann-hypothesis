module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.FreeOfNeat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2BaseAct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Faith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2IwLev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LevEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NtExpand
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PiBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WeightVariablesExist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTeichEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CLocConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsHeckeIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaCtrlMu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2ActEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2SmulKey
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModuleStructureOfCommuting
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NonemptyUnitaryHeckeParts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWtBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeForUp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VLPiPts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.BasePack
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LocCFT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.PhiAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ProModularRingExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2LocEq

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

attribute [local instance 2000] UpperTheory.V.W.coefLocal
open UpperTheory.V.Hi.LvR
private theorem hida_lq_lc {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid F O n) : IsLocallyConstant fun g : F.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1) := by
  have h : IsLocallyConstant fun (g : F.G₀) (i : Fin n) => r.chib i g :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
      have := Filter.eventually_all.2 fun i => (JEx.lc_of_open _ (r.chib_open i)).eventually_eq x
      exact this.mono fun y hy => funext hy
  have e : (fun g : F.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1)) =
      (fun t : Fin n → (ResidueField O)ˣ => (Matrix.diagonal fun i => (t i : ResidueField O)).charpoly) ∘
        fun (g : F.G₀) (i : Fin n) => r.chib i g := by
    funext g
    rw [Resid.Dbar, (AlgebraTools.Det.repApi _).2.1]
    rfl
  rw [e]
  exact h.comp _
private theorem hida_lq_dense {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (hc : Continuous p)
    (hs : Function.Surjective p) {S : Set X} (hS : Dense S) {T : Set Y} (h : ∀ x ∈ S, p x ∈ T) : Dense T :=
  (hs.denseRange.dense_image hc hS).mono (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)
private theorem hida_levelUR2LocEq :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (r : Resid V₀.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q₀ ι Λ) (K₀ : (hset Q₀ R.τ₀).Lev) (K : (hset Q R.τ₀).Lev), V₀.S' = s.S → (∀ q, K.1 q = KO ((Q.wq q).adicCompletion L) (Fin n)) → ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q R.τ₀).Op → (hset Q₀ R.τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q R.τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → (∀ i, (hset Q R.τ₀).op Λ.Λ i = (hset Q₀ R.τ₀).op Λ.Λ (j i)) ∧ ∀ f : (hset Q₀ R.τ₀).X.Fn Λ.Λ R.m, f ∈ (hset Q R.τ₀).MK (A := Λ.Λ) R.θ (fun i => R.a (j i)) K ↔ f ∈ (hset Q₀ R.τ₀).MK R.θ R.a K₀ := by
  exact @_root_.UpperTheory.V.Hi.levelUR2LocEq_alt
private theorem base_object_hom_ext {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (T : Type) [CommRing T] [Algebra O T] [Alg.IsCO O T] (f g : B.B →ₐ[O] T)
    (h1 : B.u.D.map f.toRingHom = B.u.D.map g.toRingHom)
    (h2 : ∀ v i, W.pushCh f.toRingHom (B.u.ψ v i) = W.pushCh g.toRingHom (B.u.ψ v i)) : f = g := by
  obtain ⟨p, hp⟩ := W.exists_determinantPair_map_of_algHom l F O n r B.B T g B.u
  exact (B.univ T p).unique ⟨h1.trans hp.1, fun v i => (h2 v i).trans (hp.2 v i)⟩ hp
private theorem lam_val {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (Λ : LamObj r) {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair r R) (v : F.Vl) (i : Fin n)
    (γ : F.Gv v) (hγ : γ ∈ F.Iv v) (a : O) (x : Λ.Λ) (hx : x = algebraMap O Λ.Λ a * (Λ.κ v i ⟨γ, hγ⟩ : Λ.Λˣ) - 1) :
    Λ.toPair p x = algebraMap O R a * (p.ψ v i γ : R) - 1 := by
  have e : Λ.toPair p (Λ.κ v i ⟨γ, hγ⟩ : Λ.Λˣ) = (p.ψ v i γ : R) :=
    by have h := congrArg Units.val (DFunLike.congr_fun (Λ.toPair_spec r p v i) (⟨γ, hγ⟩ : F.Iv v)); exact h
  rw [hx, map_sub, map_mul, map_one, AlgHom.commutes, e]
private theorem eq_sub {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (P N N₀ : Submodule A M) (Z : Submodule A P)
    (h : Z.map P.subtype = N) (h₀ : ∀ f, f ∈ N ↔ f ∈ N₀) :
    ∃ e : Z ≃+ N₀, ∀ z : Z, (e z : M) = (z : P) ∧ ((z : P) : M) ∈ N := by
  have e2 : Z.map P.subtype = N₀ := h.trans (Submodule.ext h₀)
  exact ⟨((Z.equivMapOfInjective P.subtype P.injective_subtype).trans (LinearEquiv.ofEq _ _ e2)).toAddEquiv,
    fun z => ⟨rfl, h ▸ Submodule.mem_map_of_mem z.2⟩⟩
private theorem under_eq {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {A : ValuationSubring Ω} {w : Plc L} {v : Plc (Lp L)} (hw : IsPlaceOver A w) (hv : IsPlaceOver A v) :
    w.under (𝓞 (Lp L)) = v := by
  ext x
  exact (hw (algebraMap _ (𝓞 L) x)).symm.trans (hv x)

private theorem umod_abs (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c) (hax : H.Ax)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hw : H.IsWt θ) (a : H.Op → c.O) [DecidableEq H.Q]
    (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) (haut : H.AutomorphicHeckeSet ι P) (lam0 : Wt L l n) (hl0 : lam0 ∈ H.admitted) (hd : H.DenseWt θ lam0)
    (hneat : ∀ K, H.X.Neat (H.lev K))
    (hf : ∀ (K : H.Lev) (k : GV n H.wq) (j : GV n H.wq →* H.X.Ub), (∀ q g, j (Pi.mulSingle q g) = H.sec (H.wq q) g) → j k ∈ H.lev K → k ∈ Subgroup.pi Set.univ K.1)
    (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R)
    (hu : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g)
    (hJ : ∀ K, ∃ J, H.IsJ θ a K D₀ ψ₀ lam J) :
    ∃ (ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))) (α : R →+* Module.End A (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧ (∀ K : H.Lev, (fixd ρ (Subgroup.pi Set.univ K.1)).map (Submodule.subtype _) = H.MK θ a K ∧ Module.Finite A (fixd ρ (Subgroup.pi Set.univ K.1))) ∧ (∀ (K K' : H.Lev) [((Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1)).Normal], (∀ q, K'.1 q ≤ K.1 q) → ∃ ρ' : Representation A (Subgroup.pi Set.univ K.1 ⧸ (Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1)) (fixd ρ (Subgroup.pi Set.univ K'.1)), (∀ (u : Subgroup.pi Set.univ K.1) f, (ρ' (u : _ ⧸ _) f).1 = ρ u.1 f) ∧ Module.Projective (MonoidAlgebra A (Subgroup.pi Set.univ K.1 ⧸ (Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1))) ρ'.asModule) ∧ (∀ (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t (y : H.MK θ a K) (z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (z : H.X.Fn A H.m) = y → (α t z : H.X.Fn A H.m) = ((f t : Module.End A (H.MK θ a K)) y : H.MK θ a K)) ∧ ∀ z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), z ≠ 0 → ∃ (x : R →+* Qbar l) (ρx : H.Gq →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n H.wq) Y) (sp : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)) →+ Y) (σ : ∀ q, SmIrr (GLw n (H.wq q))), sp z ≠ 0 ∧ Continuous ρx ∧ D₀.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ q, IsoSum (π.comp (MonoidHom.mulSingle (fun q => GLw n (H.wq q)) q)) ⊤ (σ q)) ∧ ∀ q (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (H.wq q)) (rc : IrrGL (k := (H.wq q).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc → _root_.UpperTheory.V.Z.Win.WOT ι (ρx.comp H.prj) (rc (algNorm (σ q))) := by
  obtain ⟨ρ, h1, h2, h3, h4⟩ := piBasic L Ω l n c H hax A θ hw a
  obtain ⟨α, a1, a2, a3⟩ := _root_.UpperTheory.V.Hi.levelUR2ActEx_alt hN L Ω l n c H hax A θ hw a ρ h1 h2 h3 R D₀ ψ₀ lam hu hJ
  refine ⟨ρ, α, a1, a2, fun K => ⟨h2 K, ?_⟩, fun K K' _ hle => h4 hneat K K' hle fun k _ j hj hk => hf K' k j hj hk, a3, ?_⟩
  · have hfin : Module.Finite A (H.MK θ a K) := ((hiComm L Ω l n c H hax A θ hw K).2.2.2 a).2.1
    let e := (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) (fixd ρ (Subgroup.pi Set.univ K.1))).trans
      (LinearEquiv.ofEq _ _ (h2 K))
    exact Module.Finite.equiv e.symm
  · exact _root_.UpperTheory.V.Hi.piPts_n_alt hN L Ω l n c H hax A θ hw ι P haut lam0 hl0 hd a ρ h1 R D₀ α fun K _ _ => by
      obtain ⟨f, hf1, hf2⟩ := a3 K
      exact ⟨f.toRingHom, _, hf1, hf2⟩

private theorem s1 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V0)) (Q : QData V) [_dq : DecidableEq Q.Q] (hsub : V0.S' ⊆ V.S') (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (B' : UniversalOrdinaryDeterminantRing (rUp h)) :
    ∃ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O) (lam : A →ₐ[c.O] B'.B), (hset Q τ₀).IsWt θ' ∧ @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ ∧
      (∀ i, a' i = a (opUp Q0 Q hsub τ₀ i)) ∧ (∀ v i (γ : V0.frame.Gv v) (hγ : γ ∈ V0.frame.Iv v), lam (κ v i ⟨γ, hγ⟩ : Aˣ) = (@id (Dec (F := L) (s.A v.1) →* B'.Bˣ) (B'.u.ψ v i) γ : B'.Bˣ)) ∧ (∀ w, (hset Q τ₀).DenseWt θ' w) ∧ ∀ K, ∃ J, (hset Q τ₀).IsJ θ' a' K B'.u.D B'.u.ψ lam J := by
  let κ' : ∀ v, Fin n → V.frame.Iv v →* Aˣ := κ
  have hi' : W.IsInert (rUp h) κ' := (lamUp h ⟨A, κ, hi, hu⟩).inert
  have hu' : ∀ (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R] (κ'' : ∀ v, Fin n → V.frame.Iv v →* Rˣ), W.IsInert (rUp h) κ'' →
      ∃! f : A →ₐ[c.O] R, ∀ v i, W.pushCh (f : A →+* R) (κ' v i) = κ'' v i := (lamUp h ⟨A, κ, hi, hu⟩).univ
  let θ' : (hset Q τ₀).X.I.T →* Aˣ := θ
  have th' : IsTheta Q τ₀ (⟨A, κ', hi', hu'⟩ : LamObj (rUp h)) θ' := fun v i x g hg y h1 h2 => th v i x g hg y h1 h2
  have hw' : (hset Q τ₀).IsWt θ' := ⟨cont_up Q0 Q τ₀ θ hw.cont, fun K => free_of_neat _ _ _ _ (neatU l L Ω s n hn V Q c m τ₀ K)⟩
  refine ⟨θ', fun i => a (opUp Q0 Q hsub τ₀ i), LamObj.toPair ⟨A, κ', hi', hu'⟩ B'.u, hw', rfl, fun _ => rfl, fun v i γ hγ => ?_,
    (_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta P.litN l L Ω s n hn V Q c m τ₀ (rUp h) ⟨A, κ', hi', hu'⟩ θ' th').2,
    _root_.UpperTheory.V.Hi.exists_hecke_ideal P l L Ω s n hn V Q c (rUp h) ι B' ⟨A, κ', hi', hu'⟩
      ⟨m, τ₀, _root_.UpperTheory.V.Hi.LvR.type_for_r_up_of_type_for h hp ι τ₀ ty, θ', th', hw', fun i => a (opUp Q0 Q hsub τ₀ i), res_up h Q0 Q hsub hp τ₀ a rs⟩⟩
  have e0 := DFunLike.congr_fun (LamObj.toPair_spec (rUp h) ⟨A, κ', hi', hu'⟩ B'.u v i) (⟨γ, hγ⟩ : V.frame.Iv v)
  exact congrArg Units.val e0

private theorem s2 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V0)) (Q : QData V) [_dq : DecidableEq Q.Q] (hsub : V0.S' ⊆ V.S') (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (_B' : UniversalOrdinaryDeterminantRing (rUp h)) (hS : V0.S' = s.S) (K0 : (hset Q0 τ₀).Lev)
    (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O) (e1 : @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ) (e2 : ∀ i, a' i = a (opUp Q0 Q hsub τ₀ i)) :
    (∀ i, (hset Q τ₀).op A i = (hset Q0 τ₀).op A (opUp Q0 Q hsub τ₀ i)) ∧
      ∀ f : (hset Q0 τ₀).X.Fn A m, f ∈ (hset Q τ₀).MK θ' a' (kMax Q τ₀) ↔ f ∈ (hset Q0 τ₀).MK θ a K0 := by
  obtain rfl : a' = fun i => a (opUp Q0 Q hsub τ₀ i) := funext e2
  subst θ'
  have hloc := hida_levelUR2LocEq P l L Ω s n hn V0 V Q0 Q c r ι ⟨A, κ, hi, hu⟩ ⟨m, τ₀, ty, θ, th, hw, a, rs⟩ K0 (kMax Q τ₀) hS (fun _ => rfl)
    (p0 h) (continuous_levelChangeBaseGroupHom h) (surjective_levelChangeBaseGroupHom h) (levelChangeBaseGroupHom_apply_projection h hp) (opUp Q0 Q hsub τ₀) (fun _ => rfl) fun _ _ => ⟨_, rfl⟩
  exact hloc

private theorem s3 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V0)) (Q : QData V) [dq : DecidableEq Q.Q] (hsub : V0.S' ⊆ V.S') (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (B' : UniversalOrdinaryDeterminantRing (rUp h)) (hS : V0.S' = s.S) (K0 : (hset Q0 τ₀).Lev) (B : UniversalOrdinaryDeterminantRing r) (β : B'.B →ₐ[c.O] B.B) (hβ1 : B'.u.D.map β.toRingHom = B.u.D.comap (p0 h))
    (hβ2 : ∀ (v : Vl l L) i, @Eq (Dec (F := L) (s.A v.1) →* B.Bˣ) (W.pushCh β.toRingHom (B'.u.ψ v i)) (B.u.ψ v i))
    (μ : B.B →+* Module.End A ((hset Q0 τ₀).MK θ a K0))
    (hμ : (hset Q0 τ₀).MK θ a K0 = ⊥ ∨ ∃ (_ : Fact (CommOn ((hset Q0 τ₀).MK θ a K0) ((hset Q0 τ₀).op A))) (_ : Alg.IsCO c.O ((hset Q0 τ₀).TK θ a K0)) (f : B.B →ₐ[c.O] (hset Q0 τ₀).TK θ a K0), (hset Q0 τ₀).IsMap θ a K0 B.u.D B.u.ψ f ∧ ∀ t, μ t = (f t : Module.End A ((hset Q0 τ₀).MK θ a K0))) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module A M) (ρ : Representation A (GV n Q.wq) M) (α : B'.B →+* Module.End A M) (lam : A →ₐ[c.O] B'.B), (∀ v i (γ : V0.frame.Gv v) (hγ : γ ∈ V0.frame.Iv v), lam (κ v i ⟨γ, hγ⟩ : Aˣ) = (@id (Dec (F := L) (s.A v.1) →* B'.Bˣ) (B'.u.ψ v i) γ : B'.Bˣ)) ∧
      (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧
      (∀ K : ∀ q, Subgroup (GLw n (Q.wq q)), (∀ q, IsOpen (K q : Set (GLw n (Q.wq q))) ∧ IsCompact (K q : Set (GLw n (Q.wq q)))) → Module.Finite A (fixd ρ (Subgroup.pi Set.univ K))) ∧
      (∀ K K' : ∀ q, Subgroup (GLw n (Q.wq q)), (∀ q, IsOpen (K q : Set (GLw n (Q.wq q))) ∧ IsCompact (K q : Set (GLw n (Q.wq q)))) → (∀ q, IsOpen (K' q : Set (GLw n (Q.wq q))) ∧ IsCompact (K' q : Set (GLw n (Q.wq q)))) → ∀ [((Subgroup.pi Set.univ K').subgroupOf (Subgroup.pi Set.univ K)).Normal], (∀ q, K' q ≤ K q) →
        ∃ ρ' : Representation A (Subgroup.pi Set.univ K ⧸ (Subgroup.pi Set.univ K').subgroupOf (Subgroup.pi Set.univ K)) (fixd ρ (Subgroup.pi Set.univ K')), (∀ (u : Subgroup.pi Set.univ K) f, (ρ' (u : _ ⧸ _) f).1 = ρ u.1 f) ∧
          Module.Projective (MonoidAlgebra A (Subgroup.pi Set.univ K ⧸ (Subgroup.pi Set.univ K').subgroupOf (Subgroup.pi Set.univ K))) ρ'.asModule) ∧
      (∃ e0 : fixd ρ (Subgroup.pi Set.univ fun q => KO ((Q.wq q).adicCompletion L) (Fin n)) ≃+ (hset Q0 τ₀).MK θ a K0, ∀ t (x x' : fixd ρ (Subgroup.pi Set.univ fun q => KO ((Q.wq q).adicCompletion L) (Fin n))), (x' : M) = α t x → e0 x' = μ (β t) (e0 x)) ∧
      ∀ z : M, z ≠ 0 → ∃ (x : B'.B →+* Qbar l) (ρx : V.frame.G₀ →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n Q.wq) Y) (sp : M →+ Y) (σ : ∀ q, SmIrr (GLw n (Q.wq q))), sp z ≠ 0 ∧ Continuous ρx ∧ B'.u.D.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ q, IsoSum (π.comp (MonoidHom.mulSingle (fun q => GLw n (Q.wq q)) q)) ⊤ (σ q)) ∧ ∀ q (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (Q.wq q)) (rc : IrrGL (k := (Q.wq q).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc → _root_.UpperTheory.V.Z.Win.WOT ι (ρx.comp V.pr) (rc (algNorm (σ q))) := by
  obtain ⟨θ', a', lam, hw', e1, e2, hl, hd, hJ⟩ := s1 P l L Ω s n hn V0 Q0 c r ι A κ hi hu m τ₀ ty θ th hw a rs V h Q hsub hp B'
  obtain ⟨hop, hM⟩ := s2 P l L Ω s n hn V0 Q0 c r ι A κ hi hu m τ₀ ty θ th hw a rs V h Q hsub hp B' hS K0 θ' a' e1 e2
  obtain ⟨ρ, α, h1, h2, h3, h4, h5, h6⟩ := @umod_abs P.litN L Ω _ _ _ _ _ l _ n c (hset Q τ₀) (_root_.UpperTheory.V.Hi.axU_s P.litN l L Ω s n hn V Q c m τ₀) A _ _ _ θ' hw' a' dq ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties (rUp h) ι)
    (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor P l L Ω s n hn V Q c (rUp h) ι m τ₀ (_root_.UpperTheory.V.Hi.LvR.type_for_r_up_of_type_for h hp ι τ₀ ty)) (fun _ => ⟨0, fun _ _ _ => le_rfl⟩) trivial (hd _) (neatU l L Ω s n hn V Q c m τ₀)
    (levelUR2Faith l L Ω s n hn V Q c m τ₀) B'.B _ _ B'.u.D B'.u.ψ lam (base_object_hom_ext B') hJ
  have key := _root_.UpperTheory.V.Hi.levelUR2SmulKey_alt P.litN l L Ω s n hn V0 V Q0 Q c m τ₀ A θ hw a K0 (kMax Q τ₀)
    (p0 h) (continuous_levelChangeBaseGroupHom h) (surjective_levelChangeBaseGroupHom h) (levelChangeBaseGroupHom_apply_projection h hp) (opUp Q0 Q hsub τ₀) (fun _ => rfl) (fun _ _ => ⟨_, rfl⟩)
    θ' a' hw' e1 e2 hop hM B.B B'.B B.u.D B.u.ψ B'.u.D B'.u.ψ β hβ1 hβ2
    (base_object_hom_ext B') μ hμ (fun t y => (α t ⟨y.1, Submodule.mem_iSup_of_mem _ y.2⟩).1) (fun t => congrArg Subtype.val (map_zero (α t)))
    (fun {i1} {i2} => (@h5 (kMax Q τ₀) i1 i2).elim fun f hf => ⟨f, hf.1, fun t y => hf.2 t y _ rfl⟩)
  obtain ⟨e0, he0⟩ := eq_sub _ _ ((hset Q0 τ₀).MK θ a K0) _ (h3 (kMax Q τ₀)).1 hM
  let S : Submodule A ((hset Q τ₀).X.Fn A m) := ⨆ K, (hset Q τ₀).MK θ' a' K
  refine ⟨(S : Type), S.addCommGroup, S.module, ρ, α, lam, hl, h1, h2, ?_, ?_, ?_, ?_⟩
  · intro K hK
    exact (h3 ⟨K, hK⟩).2
  · intro K K' hK hK' hN hle
    obtain ⟨ρ', hact, hproj⟩ := @h4 ⟨K, hK⟩ ⟨K', hK'⟩ hN hle
    refine ⟨ρ', ?_, ?_⟩
    · intro u f
      exact hact u f
    · apply hproj
  · refine ⟨e0, fun t x x' hx => Subtype.ext ?_⟩
    exact ((he0 x').1.trans (congrArg Subtype.val hx)).trans (key t ⟨x.1.1, (he0 x).2⟩ (e0 x) (he0 x).1.symm)
  · exact h6

private theorem s4 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (B : UniversalOrdinaryDeterminantRing r) (K : (hset Q0 τ₀).Lev) (hS : V0.S' = s.S) (J : Ideal B.B)
    (hJ : (hset Q0 τ₀).IsJ θ a K B.u.D B.u.ψ (LamObj.toPair ⟨A, κ, hi, hu⟩ B.u : A →ₐ[c.O] B.B) J) : _root_.UpperTheory.V.Th.LevelIdealCondition B J := by
  have hN := P.litN
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have hA0 := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V0 Q0 c m τ₀
  obtain ⟨wv, e, hwt⟩ : ∃ (wt : Pa.WtVars (Pa.locOf r) c.O n (n * Module.finrank ℚ (Lp L))) (e : Pa.abelian₂ c.O Empty (n * Module.finrank ℚ (Lp L)) ≃ₐ[c.O] A), ∀ k, ∃ hγ : wt.γ k ∈ V0.frame.Iv (wt.v k), residue c.O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField c.O) = 1 ∧ e (MvPowerSeries.X (.inr k)) = algebraMap c.O A (wt.c k) * (κ (wt.v k) (wt.i k) ⟨wt.γ k, hγ⟩ : Aˣ) - 1 :=
    levelUR2WtVars l L Ω s n V0 c r B ⟨A, κ, hi, hu⟩ (W.locCFT hN.aut.art hC l L Ω s)
  choose hγ hres hX using hwt
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ := levelUR2BaseAct L Ω l n c _ hA0 A θ hw a K B.B B.u.D B.u.ψ _ J hJ
  obtain ⟨-, hfin, hfree⟩ := (hiComm L Ω l n c _ hA0 A θ hw K).2.2.2 a
  obtain ⟨b, eb, hb, heb, hsub0⟩ := Th.AnnihilatorQuotientFinite.basePack l L Ω s V0 c.O n r B J _ wv A e (LamObj.toPair ⟨A, κ, hi, hu⟩ B.u) hres
    (fun k => lam_val ⟨A, κ, hi, hu⟩ B.u _ _ _ (hγ k) _ _ (hX k)) _ μ hμ1 hμ2
  subst hb
  refine ⟨b, fun V h q v w Bq hp hv hvS hV hw' hBv _ => ?_, hγ, fun x h ha t ht k hk y => ?_⟩
  swap
  · obtain ⟨⟨lam, hl⟩, hb⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight hN l L Ω s n hn V0 Q0 c m τ₀ r B ⟨A, κ, hi, hu⟩ θ th h ha.1
    have har := (hb lam hl (Th.barPt B x)).1.1 ha
    obtain ⟨y, rfl⟩ := eb.surjective y
    rw [← heb, hsub0]
    exact _root_.UpperTheory.V.Th.AnnihilatorQuotientFinite.ctrlMu_of_arith_weight L Ω l n c _ hA0 A θ hw ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι) (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor P l L Ω s n hn V0 Q0 c r ι m τ₀ ty)
      (x.comp (LamObj.toPair ⟨A, κ, hi, hu⟩ B.u)) lam (Set.mem_univ _) har a K B.B B.u.D B.u.ψ μ hμ3 t ht k
      (fun y => (hsub0 x _).1 (by rw [heb]; exact hk _)) y
  obtain rfl : (fun j => (w j).under (𝓞 (Lp L))) = v := funext fun j => under_eq (hw' j) (hBv j)
  have hsub : V0.S' ⊆ V.S' := hS ▸ V.sub
  obtain ⟨p', hp1, hp2⟩ := pairUp h hn hp B.u
  obtain ⟨B'⟩ := W.b0Ex (W.phiAll hC) l L Ω s V c n (rUp h) B.B ⟨p'⟩
  obtain ⟨β, hβ, -⟩ := B'.univ B.B p'
  have hβ1 : B'.u.D.map β.toRingHom = B.u.D.comap (p0 h) := hβ.1.trans hp1
  have hβ2 : ∀ (v : Vl l L) i, @Eq (Dec (F := L) (s.A v.1) →* B.Bˣ) (W.pushCh β.toRingHom (B'.u.ψ v i)) (B.u.ψ v i) :=
    fun v i => (hβ.2 v i).trans (hp2 v i)
  obtain ⟨M, addM, modM, ρ, α, lam, hl, h1, h2, h3, h4, ⟨e0, he0⟩, h6⟩ := @s3 P l _ L Ω _ _ _ _ _ _ s n hn V0 Q0 c r ι A _ _ _ κ hi hu m τ₀ ty θ th hw a rs
    V h (qUp V w hv hvS hV) (instDecidableEqFin q) hsub hp B' hS K B β hβ1 hβ2 μ hμ3
  obtain ⟨hI, hNm⟩ := levelUR2IwLev l L n q w
  let I (j : Fin q) := AlgebraTools.iwC ((w j).adicCompletion L) n ⊤
  let I₁ (j : Fin q) := AlgebraTools.iwC ((w j).adicCompletion L) n (Pa.ellC l _)
  have hI₁ (j : Fin q) : IsOpen (I₁ j : Set (GLw n (w j))) ∧ IsCompact (I₁ j : Set (GLw n (w j))) :=
    ⟨(hI j _).1, (hI j _).2.1⟩
  obtain ⟨ρ', h7, h8⟩ := @h4 I I₁ (fun j => ⟨(hI j ⊤).1, (hI j ⊤).2.1⟩)
    hI₁ hNm fun j => (hI j _).2.2
  have hfin₁ := h3 I₁ hI₁
  have pack := @_root_.UpperTheory.V.Hi.levelUR2ModPack_alt l _ L Ω _ _ _ _ _ _ s V0 c.O _ _ _ n r B J _ b
    V h q w (rN h) (rN_compat h) B'.B _ _ _ (pairN h B'.u) A _ _ e lam
  refine @pack ?_ β ?_ M addM modM ρ α ?_ ?_ ?_ hNm ρ' ?_ ?_ ?_ ?_ ι ?_
  · intro k
    rw [hX k, map_sub, map_mul, map_one, AlgHom.commutes]
    exact congrArg (fun z => algebraMap c.O B'.B (b.wt.c k) * z - 1) (hl (b.wt.v k) (b.wt.i k) (b.wt.γ k) (hγ k))
  · exact ⟨hβ1, hβ2⟩
  · exact h1
  · exact h2
  · exact hfin₁
  · intro u f
    exact h7 u f
  · apply h8
  · exact e0.trans eb
  · intro t x x' hx
    exact (congrArg eb (he0 t x x' hx)).trans (heb (β t) (e0 x))
  · exact h6

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.levelX_of_isJ_unitaryHeckeData :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → _root_.UpperTheory.V.Th.LevelIdealCondition B J := by
  intro P l _ L Ω _ _ _ _ _ _ s n hn V0 Q0 c r ι B Λ R K hS J hJ
  obtain ⟨A, κ, hi, hu⟩ := Λ
  obtain ⟨m, τ₀, ty, θ, th, hw, a, rs⟩ := R
  exact s4 P l L Ω s n hn V0 Q0 c r ι A κ hi hu m τ₀ ty θ th hw a rs B K hS J hJ
end
