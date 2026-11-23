module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevOffType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReGLMemLevelVL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMLevJ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepBeforeClNonempty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtRec
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mem.Col2.TwistLevel


private theorem mem_congr {A S : Type*} [Membership A S] {U V : S} {x y : A}
    (hUV : U = V) (hxy : x = y) : x ∈ U ↔ y ∈ V :=
  Iff.of_eq (congrArg₂ (fun (K : S) (z : A) => z ∈ K) hUV hxy)

private theorem character_eq_of_local_eq {G H : Type*} [Group G] [Group H]
    {V : Type*} {L : V → Type*} [∀ v, Group (L v)]
    (p : ∀ v, G →* L v) (χ : G →* H)
    (htriv : ∀ x, (∀ v, p v x = 1) → χ x = 1)
    {x y : G} (h : ∀ v, p v x = p v y) : χ x = χ y :=
  mul_inv_eq_one.mp ((χ.map_mul_inv x y).symm.trans
    (htriv (x * y⁻¹) fun v => ((p v).map_mul_inv x y).trans (mul_inv_eq_one.mpr (h v))))

set_option maxHeartbeats 64000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_levJ_cosets_of_further : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → (∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ (W : ∀ v, v ∈ Q → Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) (ψ : (∀ v : Q, ↥(W v.1 v.2)) →* ℂˣ), (∀ v hv, W v hv ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0) ∧ (∀ v hv, ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ W v hv) ∧ (∀ β v hv, (K β).lev.Uloc v ≤ (W v hv).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ∧ (∀ β v hv, ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v hv)).FiniteIndex) ∧ (∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(W v.1 v.2)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z)) → Nonempty (TwLevJ I l Z F Q u a chOf K) := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hUl hchi hFur
  classical
  let D := I.rec7 l Z
  let i := B.R.m - 1
  let e : (B.sp.X i).rank = B.R.N i := rankN D i (Nat.sub_le _ _)
  let gram : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E := gramN D i (Nat.sub_le _ _)
  let Place := HeightOneSpectrum (𝓞 B.host.F)
  let RAf := AfE B.host.F B.host.E
  let Rv (v : Place) := B.host.E ⊗[B.host.F] v.adicCompletion B.host.F
  let reA := reGL e RAf
  let reV (v : Place) := reGL e (Rv v)
  let srcLoc (v : Place) : GL (Fin (B.sp.X i).rank) RAf →* GL (Fin (B.sp.X i).rank) (Rv v) :=
    bc (prV (E := B.host.E) v)
  let dstLoc (v : Place) : GA B (B.R.N i) →* GL (Fin (B.R.N i)) (Rv v) :=
    bc (prV (E := B.host.E) v)
  have hQb : ∀ v ∈ Q, ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal :=
    fun v hv => underQ_prime_to_bad I hOk l u a v ((hQ v).1 hv)
  obtain ⟨H0, hH0L, hH0U⟩ :
      ∃ H0 : Formalism.L2.Herm.StepLevel B.sp.cm (B.sp.X i) B.host.g (B.T u) B.R.f,
        (F u).levJ.Lb = reL e H0.Lb ∧
        ∀ v : Place, (F u).levJ.Uloc v = (H0.Uloc v).map (reV v).toMonoidHom :=
    GlobalTheory.Mem.Col2.TC.levJ_herm_level I hOk hPins l Z u (F u) (hStd u) h1
  obtain ⟨W, ψ, hWl, hWQ, hWle, hWfi, hψ⟩ := hFur H0.Lb hH0L
  choose w hw using fun β0 : Ch0 u (B.R.m - 1) => GlobalTheory.Mem.Col2.TC.chartLev_stab_vec I hOk hPins l Z u (F u) (hStd u) (hfr u) h1 β0
  have hRed := GlobalTheory.Mem.Col2.TC.LevJRed.redM_levJ I hOk hPins l Z u (F u) (hStd u)
  obtain ⟨J, hJLb, hmemU, hJUl⟩ : ∃ J : Formalism.L2.Herm.StepLevelQ B.sp.cm (B.sp.X i) B.host.g (B.T u) B.R.f Q,
      J.Lb = H0.Lb ∧ (∀ x, x ∈ J.U ↔ x ∈ Formalism.L2.Herm.UAf B.sp.cm (B.sp.X i) ∧
      ∀ v, srcLoc v x ∈ ulocQ H0 Q W v) ∧ ∀ v, J.Uloc v = ulocQ H0 Q W v :=
    ⟨mkLevQ H0 Q W hWl hWQ (fun v hv i => (hQb v hv).2 i) (fun v hv => (hQb v hv).1), rfl, fun x => Iff.rfl, fun v => rfl⟩
  have hUP (x : GL (Fin (B.sp.X i).rank) RAf) :
      reA x ∈ UPts B.sp.cm.sig gram (FiniteAdeleRing (𝓞 B.host.F) B.host.F) ↔
      x ∈ Formalism.L2.Herm.UAf B.sp.cm (B.sp.X i) :=
    reGL_mem_UPts B.sp.cm.sig e (B.sp.X i).gram gram rfl _ x
  have hbc : ∀ v (y : GL (Fin (B.sp.X i).rank) RAf),
      dstLoc v (reA y) = reV v (srcLoc v y) :=
    fun v y => Formalism.L2.G.bc_reGL e (prV (E := B.host.E) v) y
  have hmap (v : Place) (H : Subgroup (GL (Fin (B.sp.X i).rank) (Rv v))) (y : GL (Fin (B.sp.X i).rank) (Rv v)) :
      reV v y ∈ H.map (reV v).toMonoidHom ↔ y ∈ H :=
    Subgroup.mem_map_iff_mem (reV v).injective
  have hgQ : ∀ j v, (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal → v ∉ Q := fun j v hv hq => (hQb v hq).2 j hv
  have hJoff : ∀ (κ : J.U) v, v ∉ Q → reV v (srcLoc v κ.1) ∈ (F u).levJ.Uloc v := fun κ v hv => by
    have hLoc := (mem_congr (ulocQ_neg H0 Q W hv) rfl).mp (((hmemU _).mp κ.2).2 v)
    exact (mem_congr (hH0U v) rfl).mpr ((hmap v _ _).mpr hLoc)

  obtain ⟨k, hRd, -⟩ := id hR
  obtain ⟨k0, hR0⟩ := (hStd u).mid (B.R.m - 1) h1 (succ_pred_m B.R)
  let ι : Type := Σ j : Fin 2, {v : Place // (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal}
  have : Finite ι := by
    have : ∀ j : Fin 2, Finite {v : Place // (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal} := fun j => by
      have hne : (B.host.g j : 𝓞 B.host.F) ≠ 0 := Nat.cast_ne_zero.2 (l.pr.g_prime j).ne_zero
      have hfin := Ideal.finite_factors (I := Ideal.span {(B.host.g j : 𝓞 B.host.F)}) (by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hne)
      have hf : Set.Finite {v : Place | (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal} := hfin.subset (by
        intro v hv
        exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv))
      exact hf.to_subtype
    exact Finite.instSigma
  have : ∀ p : ι, Finite (kv B.host.F p.2.1) := fun p => Formalism.UG.P.glint_finite_residueField p.2.1
  let V := ∀ p : ι, Fin (B.R.N i) → kv B.host.F p.2.1
  have hfinV : Finite V := Pi.finite
  let φ (v : Place) : J.U →* GL (Fin (B.R.N i)) (Rv v) :=
    (reV v).toMonoidHom.comp ((srcLoc v).comp J.U.subtype)
  let redAt (p : ι) (x : GL (Fin (B.R.N i)) (Rv p.2.1)) :
      Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (kv B.host.F p.2.1) :=
    redM B.host.F p.2.1 ((F u).gl.mat p.1 p.2.1 p.2.2 ((F u).glevJ.fr p.1 p.2.1 p.2.2) x)
  let ρ (κ : J.U) := fun p : ι => redAt p (φ p.2.1 κ)
  have hρ1 : ρ 1 = 1 := funext fun p =>
    (congrArg (redAt p) (φ p.2.1).map_one).trans (hRed p.1 p.2.1 p.2.2).1
  have hρm (a b : J.U) : ρ (a * b) = ρ a * ρ b := funext fun p =>
    (congrArg (redAt p) ((φ p.2.1).map_mul a b)).trans
      ((hRed p.1 p.2.1 p.2.2).2 _ (hJoff a p.2.1 (hgQ p.1 p.2.1 p.2.2))
        _ (hJoff b p.2.1 (hgQ p.1 p.2.1 p.2.2)))
  let actV : MulAction J.U V := actOfRed ρ hρ1 hρm

  have hWmem (κ : J.U) (v : Q) : srcLoc v.1 κ.1 ∈ W v.1 v.2 :=
    (mem_congr (ulocQ_pos H0 Q W v.2) rfl).mp (((hmemU _).1 κ.2).2 v.1)
  let zQ : J.U →* ∀ v : Q, ↥(W v.1 v.2) :=
    MonoidHom.pi fun v => (((srcLoc v.1).comp J.U.subtype).codRestrict (W v.1 v.2)
      fun κ => hWmem κ v)
  let Kc : Ch → ∀ v : Q, Subgroup ↥(W v.1 v.2) := fun β v =>
    (((K β).lev.Uloc v.1).comap (reV v.1).toMonoidHom).subgroupOf (W v.1 v.2)
  let Hs : Ch → Subgroup J.U := fun β => (K β).lev.U.comap (reA.toMonoidHom.comp J.U.subtype)
  let wv : Ch → V := fun β p => w (g β) p.1 p.2.1 p.2.2
  have hKloc (β : Ch) (v : Place) (hv : v ∉ Q) (x : GL (Fin (B.R.N i)) (Rv v)) :
      x ∈ (K β).lev.Uloc v ↔ x ∈ (F u).levJ.Uloc v ∧
        ∀ j (hj : (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal),
          redAt ⟨j, v, hj⟩ x *ᵥ w (g β) j v hj = w (g β) j v hj :=
    (mem_congr (hUl β v hv) rfl).trans (hw (g β) v x)
  have hH (β : Ch) (κ : J.U) :
      κ ∈ Hs β ↔ (∀ q, zQ κ q ∈ Kc β q) ∧ actV.smul κ (wv β) = wv β := by
    constructor
    · intro h
      have hU := ((K β).lev.U_eq (reA κ.1)).mp h
      have hLoc (v : Place) : φ v κ ∈ (K β).lev.Uloc v :=
        (mem_congr rfl (hbc v κ.1)).mp (hU.2 v)
      refine ⟨fun q => hLoc q.1, funext ?_⟩
      intro ⟨j, v, hv⟩
      exact ((hKloc β v (hgQ j v hv) (φ v κ)).mp (hLoc v)).2 j hv
    · rintro ⟨hQloc, hFix⟩
      apply ((K β).lev.U_eq (reA κ.1)).mpr
      refine ⟨(hUP _).mpr ((hmemU _).mp κ.2).1, fun v => ?_⟩
      apply (mem_congr rfl (hbc v κ.1)).mpr
      by_cases hv : v ∈ Q
      · exact hQloc ⟨v, hv⟩
      · exact (hKloc β v hv (φ v κ)).mpr
          ⟨hJoff κ v hv, fun j hj => congrFun hFix ⟨j, v, hj⟩⟩
  obtain ⟨Yb, hYf, aY, yb, yG, YQ, yQ, hA1, hA2, hA3, hA4, hA5⟩ :=
    @assemble J.U inferInstance Ch hCh Q inferInstance (fun q => ↥(W q.1 q.2)) inferInstance
      zQ Kc (fun β q => hWfi β q.1 q.2) V hfinV actV wv Hs hH

  have hLbK (β : Ch) : (K β).lev.Lb = reL e J.Lb := by
    have hCharts : (K β).lev.Lb = ((F u).ch i h1 (succ_pred_m B.R) (g β)).lev.Lb :=
      Submodule.ext fun x => (hRd.lb β x).trans (hR0.lb (g β) x).symm
    have hBase : (F u).levJ.Lb = reL e J.Lb :=
      hH0L.trans (congrArg (reL e) hJLb.symm)
    exact hCharts.trans (((F u).levJ_Lb h1 (g β)).trans hBase)

  have hle (β : Ch) : (K β).lev.U ≤ J.U.map reA.toMonoidHom := by
    intro x hx
    let y := reA.symm x
    have hy : reA y = x := reA.apply_symm_apply x
    have hx' := ((K β).lev.U_eq x).mp hx
    refine ⟨y, (hmemU y).mpr ⟨(hUP y).mp ((mem_congr rfl hy).mpr hx'.1), ?_⟩, hy⟩
    intro v
    have hLoc : reV v (srcLoc v y) ∈ (K β).lev.Uloc v :=
      (mem_congr rfl ((hbc v y).symm.trans (congrArg (dstLoc v) hy))).mpr (hx'.2 v)
    by_cases hv : v ∈ Q
    · exact (mem_congr (ulocQ_pos H0 Q W hv) rfl).mpr
        ((hmap v _ _).mp (hWle β v hv hLoc))
    · have hJloc := ((hKloc β v hv _).mp hLoc).1
      exact (mem_congr (ulocQ_neg H0 Q W hv) rfl).mpr
        ((hmap v (H0.Uloc v) (srcLoc v y)).mp ((mem_congr (hH0U v) rfl).mp hJloc))

  have hJg : ∀ (j : Fin 2) (v : Place) (hv : (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal),
      ∀ x ∈ levelVL B.sp.cm.sig (B.sp.X i).gram v J.Lb,
        x ∈ J.Uloc v ↔ ∃ M ∈ HSym D (B.R.N i) false v,
          M.1 = redJS F u j v hv x := by
    intro j v hv x hx
    have hx₀ := (mem_congr (congrArg (levelVL B.sp.cm.sig (B.sp.X i).gram v) hJLb) rfl).mp hx
    have hx' := (mem_congr (congrArg (levelVL B.sp.cm.sig gram v) hH0L) rfl).mpr
      ((reGL_mem_levelVL B.sp.cm.sig e _ _ rfl v H0.Lb x).mpr hx₀)
    have hLoc := (hJUl v).trans (ulocQ_neg H0 Q W (hgQ j v hv))
    exact (mem_congr hLoc rfl).trans ((hmap v _ x).symm.trans
      ((mem_congr (hH0U v).symm rfl).trans ((F u).glevJ.mem j v hv _ hx')))
  have hJo : ∀ v : Place, v ∉ Q → v ∉ badG D →
      (J.Uloc v).map (reV v).toMonoidHom = (F u).levJ.Uloc v := by
    intro v hvQ _
    exact (congrArg (Subgroup.map (reV v).toMonoidHom)
      ((hJUl v).trans (ulocQ_neg H0 Q W hvQ))).trans (hH0U v).symm

  have hoff (κ : J.U) : ∃ y ∈ (F u).levJ.U, (∀ v ∈ Q, dstLoc v y = 1) ∧
      ∀ v, v ∉ Q → dstLoc v y = φ v κ := by
    obtain ⟨y, hy, h1y, h2y⟩ := exists_off B.sp.cm.sig gram Q (reA κ.1)
      ((hUP _).mpr ((hmemU _).mp κ.2).1)
    have hOff (v : Place) (hv : v ∉ Q) : dstLoc v y = φ v κ :=
      (h2y v hv).trans (hbc v κ.1)
    refine ⟨y, ((F u).levJ.U_eq y).mpr ⟨hy, fun v => ?_⟩, h1y, hOff⟩
    by_cases hv : v ∈ Q
    · exact (mem_congr rfl (h1y v hv)).mpr (one_mem _)
    · exact (mem_congr rfl (hOff v hv)).mpr (hJoff κ v hv)
  choose off hoffU hoff1 hoff2 using hoff
  let offJ (κ : J.U) : (F u).levJ.U := ⟨off κ, hoffU κ⟩
  let ψv (v : Place) := (dstLoc v).comp (F u).levJ.U.subtype
  let χ := (F u).levJ.chi
  have htriv (x : (F u).levJ.U) (hx : ∀ v, ψv v x = 1) : χ x = 1 :=
    (F u).levJ.chi_triv x (fun v _ => hx v)
  have hoffm (κ κ' : J.U) : χ (offJ (κ * κ')) = χ (offJ κ) * χ (offJ κ') := by
    refine (character_eq_of_local_eq ψv χ htriv ?_).trans (χ.map_mul _ _)
    intro v
    refine Eq.trans ?_ ((ψv v).map_mul (offJ κ) (offJ κ')).symm
    by_cases hv : v ∈ Q
    · exact (hoff1 (κ * κ') v hv).trans
        (((congrArg₂ (· * ·) (hoff1 κ v hv) (hoff1 κ' v hv)).trans (mul_one 1)).symm)
    · exact ((hoff2 (κ * κ') v hv).trans ((φ v).map_mul κ κ')).trans
        (congrArg₂ (· * ·) (hoff2 κ v hv) (hoff2 κ' v hv)).symm
  have hoff1' : χ (offJ 1) = 1 := htriv _ fun v => by
    by_cases hv : v ∈ Q
    · exact hoff1 1 v hv
    · exact (hoff2 1 v hv).trans (φ v).map_one
  let χoff : J.U →* ℂˣ :=
    { toFun := fun κ => χ (offJ κ)
      map_one' := hoff1'
      map_mul' := hoffm }
  let chiJ : J.U →* ℂˣ := χoff * ψ.comp zQ
  have hchiJ (β : Ch) (κ : J.U) (κ' : (K β).lev.U) (h : κ'.1 = reA κ.1) :
      (K β).lev.chi κ' = chiJ κ := by
    have hκ'v (v : Place) : dstLoc v κ'.1 = φ v κ :=
      (congrArg (dstLoc v) h).trans (hbc v κ.1)
    have hκ'U := ((K β).lev.U_eq κ'.1).mp κ'.2
    have hoA := (((F u).levJ.U_eq (off κ)).mp (hoffU κ)).1
    have hoKloc (v : Place) (hv : v ∉ Q) : dstLoc v (off κ) ∈ (K β).lev.Uloc v :=
      (mem_congr rfl ((hoff2 κ v hv).trans (hκ'v v).symm)).mpr (hκ'U.2 v)
    have hoK : off κ ∈ (K β).lev.U := ((K β).lev.U_eq _).mpr ⟨hoA, fun v => by
      by_cases hv : v ∈ Q
      · exact (mem_congr rfl (hoff1 κ v hv)).mpr (one_mem _)
      · exact hoKloc v hv⟩
    let C := ((F u).ch i h1 (succ_pred_m B.R) (g β)).lev
    have hoC : off κ ∈ C.U := (C.U_eq _).mpr ⟨hoA, fun v => by
      by_cases hv : v ∈ Q
      · exact (mem_congr rfl (hoff1 κ v hv)).mpr (one_mem _)
      · exact (mem_congr (hUl β v hv) rfl).mp (hoKloc v hv)⟩
    let κo : (K β).lev.U := ⟨off κ, hoK⟩
    let δ := κ' * κo⁻¹
    let ψK (v : Place) := (dstLoc v).comp (K β).lev.U.subtype
    have hq_off (v : Place) (hv : v ∉ Q) : dstLoc v δ.1 = 1 :=
      ((ψK v).map_mul_inv κ' κo).trans (mul_inv_eq_one.mpr ((hκ'v v).trans (hoff2 κ v hv).symm))
    have hq_Q (v : Q) : reV v.1 (zQ κ v).1 = dstLoc v.1 δ.1 := by
      have h1o : ψK v.1 κo = 1 := hoff1 κ v.1 v.2
      have hδ : ψK v.1 δ = ψK v.1 κ' :=
        ((ψK v.1).map_mul_inv κ' κo).trans
          ((congrArg (fun x => ψK v.1 κ' * x⁻¹) h1o).trans
            ((congrArg (ψK v.1 κ' * ·) inv_one).trans (mul_one _)))
      exact (hκ'v v.1).symm.trans hδ.symm
    let χK := (K β).lev.chi
    have hχo : χK κo = χ (offJ κ) :=
      (hchi β κo ⟨off κ, hoC⟩ rfl (hoff1 κ)).trans
        ((F u).levJ_chi h1 (g β) ⟨off κ, hoC⟩ (offJ κ) rfl)
    have hχδ : χK δ = ψ (zQ κ) := hψ β δ (zQ κ) hq_Q hq_off
    exact (congrArg χK (inv_mul_cancel_right κ' κo).symm).trans
      ((χK.map_mul δ κo).trans
        ((congrArg₂ (· * ·) hχδ hχo).trans (mul_comm (ψ (zQ κ)) (χ (offJ κ)))))
  have hyGs : ∀ (κ : J.U) y (j : Fin 2) (v : Place) (hv : (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal),
      yG (aY.smul κ y) ⟨j, v, hv⟩ = redJS F u j v hv (srcLoc v κ.1) *ᵥ yG y ⟨j, v, hv⟩ := by
    intro κ y j v hv
    exact congrFun (hA3 κ y) ⟨j, v, hv⟩
  have hyI : ∀ y y', (fun j v hv => yG y ⟨j, v, hv⟩) = (fun (j : Fin 2) (v : Place) (hv : (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal) => yG y' ⟨j, v, hv⟩) →
      yQ y = yQ y' → y = y' := by
    intro y y' hG hQ'
    refine hA4 y y' (funext fun p => ?_) hQ'
    obtain ⟨j, v, hv⟩ := p
    exact congrFun (congrFun (congrFun hG j) v) hv
  have hyQ : ∀ (κ : J.U) y, (∀ v ∈ Q, srcLoc v κ.1 = 1) → yQ (aY.smul κ y) = yQ y := by
    intro κ y hκ
    exact hA5 κ y (funext fun q => Subtype.ext (hκ q.1 q.2))
  exact ⟨{
    levJ := J, Yb := Yb, YbFin := hYf, YbAct := aY, yb := yb, yb_orbit := hA1, lb := hLbK, «le» := hle,
    stab := hA2, chiJ := chiJ, chiJ_eq := hchiJ, J_g := hJg, J_off := hJo,
    yG := fun y j v hv => yG y ⟨j, v, hv⟩, yG_smul := hyGs,
    YQ := YQ, yQ := yQ, y_inj := hyI, yQ_off := hyQ }⟩

end GlobalTheory.Mem.Col2.TwistLevel
end
