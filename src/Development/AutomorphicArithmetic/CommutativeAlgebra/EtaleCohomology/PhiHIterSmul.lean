module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AveragingTransferKills
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.MapUSharp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiIterPull
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnOfDisj
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitPointGeneric
public import Development.AutomorphicArithmetic.EtaleIdempotents.CrystallineExpansionRelationOfScaledEndomorphism
public import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsCrystallineLatticeExpansion
public import Development.AutomorphicArithmetic.EtaleIdempotents.HeckeCorrespondenceProduct
public import Development.AutomorphicArithmetic.EtaleIdempotents.LinearCombinationTransferOfProjectorRelations
public import Development.AutomorphicArithmetic.EtaleIdempotents.NatCastPrimeNeZeroAndNotIsUnitIntegers
import GroundTheory.PAdicHodge.ACrisPhi
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section


set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

private theorem phiTL {l : ℕ} [Fact l.Prime] : phiA l (tA l) = (l : Acris l) * tA l := ACris.phi_periodT_eq_mul _

private lemma eqAbs {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] (Φ : H → H) (ph : A → A)
    (hs : ∀ c x, Φ (c • x) = ph c • Φ x) {c1 c2 c1' c2' : A} {E E' Y Y' : H} (hX : c1 • E = c2 • Y)
    (h1 : ph c1 = c1') (h2 : ph c2 = c2') (hE : Φ E = E') (hY : Φ Y = Y') : c1' • E' = c2' • Y' := by
  subst h1 h2 hE hY
  rw [← hs, ← hs, hX]

private lemma scaleAbs {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] (d : A) {c1 c2 c1' c2' : A} {E Y : H}
    (h1 : c1' = d * c1) (h2 : c2' = d * c2) (h : c1 • E = c2 • Y) : c1' • E = c2' • Y := by
  rw [h1, h2, mul_smul, mul_smul, h]

private lemma iterate_natCast {A : Type} [CommRing A] (φ : A →+* A) (n m : ℕ) :
    (φ : A → A)^[m] (n : A) = (n : A) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    exact (Function.iterate_succ_apply' _ _ _).trans ((congrArg φ ih).trans (map_natCast φ n))

private lemma phi_iter_l {l : ℕ} [Fact l.Prime] (m : ℕ) : (phiA l)^[m] (l : Acris l) = (l : Acris l) :=
  iterate_natCast (phiA l) l m

private lemma iterate_period {A : Type} [CommRing A] (φ : A →+* A) (n : ℕ) (t : A)
    (ht : φ t = (n : A) * t) (m : ℕ) : (φ : A → A)^[m] t = (n : A) ^ m * t := by
  induction m with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, ht, ← mul_assoc, ← pow_succ]

private lemma phiA_iterate_tA_of_prime {l : ℕ} [Fact l.Prime] (m : ℕ) : (phiA l)^[m] (tA l) = (l : Acris l) ^ m * tA l :=
  iterate_period (phiA l) l (tA l) phiTL m

private lemma iterate_smul_semilinear {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H]
    (φ : A →+* A) (Φ : H →ₛₗ[φ] H) (m : ℕ) (c : A) (x : H) :
    (Φ : H → H)^[m] (c • x) = (φ : A → A)^[m] c • (Φ : H → H)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Function.iterate_succ_apply', ih, LinearMap.map_smulₛₗ]

private lemma phiH_iter_smul {l : ℕ} [Fact l.Prime] (P : PAlg l ⥤ Type) (n j m : ℕ) (c : Acris l) (x : MH P n j) :
    (phiH P n j)^[m] (c • x) = ((phiA l)^[m] c) • (phiH P n j)^[m] x :=
  iterate_smul_semilinear (phiA l) ((phiMor P n).pull j) m c x

private lemma iterate_eval {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H]
    (φ : A →+* A) (Φ : H →ₛₗ[φ] H) {ι : Type} [Fintype ι] (v : ι → H) (hv : ∀ k, Φ (v k) = v k)
    (c : ι → A) (m : ℕ) : (Φ : H → H)^[m] (∑ k, c k • v k) = ∑ k, (φ : A → A)^[m] (c k) • v k := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Function.iterate_succ_apply', ih, map_sum, LinearMap.map_smulₛₗ, hv]

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private lemma phiH_evE {e : E.EtFam l K} (he : e.Good) (M : Model l K) (j lev : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j)
    (c : ι → Acris l) (m : ℕ) :
    (phiH M.P lev j)^[m] (evE e M j lev v c) = evE e M j lev v (fun k => (phiA l)^[m] (c k)) :=
  iterate_eval (phiA l) ((phiMor M.P lev).pull j) (fun k => e M lev j ((v k).lev lev))
    (fun k => he.phi M lev j ((v k).lev lev)) c m

private lemma scale_iterated_relation {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H]
    (φ : A →+* A) (Φ : H → H) (p t : A) {E E' Y : H} {a u r m d M0 : ℕ} (hM : m + d = M0)
    (hs : ∀ c x, Φ (c • x) = (φ : A → A)^[m] c • Φ x)
    (hp : (φ : A → A)^[m] p = p) (ht : (φ : A → A)^[m] t = p ^ m * t) (hE : Φ E = E')
    (hX : (p ^ a * t ^ u) • E = t ^ (u + r) • Y) :
    ((p ^ (a + M0 * u) * t ^ u) * p ^ (d * r)) • E' = (p ^ (M0 * (u + r)) * t ^ (u + r)) • Φ Y := by
  subst M0
  have c1 : (φ : A → A)^[m] (p ^ a * t ^ u) = p ^ a * (p ^ m * t) ^ u := by
    rw [iterate_map_mul φ, iterate_map_pow φ, iterate_map_pow φ, hp, ht]
  have c2 : (φ : A → A)^[m] (t ^ (u + r)) = (p ^ m * t) ^ (u + r) := by
    rw [iterate_map_pow φ, ht]
  have q1 : (p ^ (a + (m + d) * u) * t ^ u) * p ^ (d * r) =
      p ^ (d * (u + r)) * (p ^ a * (p ^ m * t) ^ u) := by ring
  have q2 : p ^ ((m + d) * (u + r)) * t ^ (u + r) =
      p ^ (d * (u + r)) * (p ^ m * t) ^ (u + r) := by ring
  exact scaleAbs _ q1 q2 (eqAbs Φ _ hs hX c1 c2 hE rfl)

private lemma eqI {e : E.EtFam l K} (he : e.Good) (M : Model l K) (j lev : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j)
    (c c' : ι → Acris l) (Y : M.MH lev j) (a u r m d M0 : ℕ) (hM : m + d = M0)
    (hc : (fun k => (phiA l)^[m] (c k)) = c')
    (hX : ((l : Acris l) ^ a * tA l ^ u) • evE e M j lev v c = tA l ^ (u + r) • Y) :
    (((l : Acris l) ^ (a + M0 * u) * tA l ^ u) * (l : Acris l) ^ (d * r)) • evE e M j lev v c' =
      ((l : Acris l) ^ (M0 * (u + r)) * tA l ^ (u + r)) • (phiH M.P lev j)^[m] Y := by
  subst c'
  exact scale_iterated_relation (H := MH M.P lev j) (phiA l) ((phiH M.P lev j)^[m]) (l : Acris l) (tA l)
    (a := a) (u := u) (r := r) hM (phiH_iter_smul M.P lev j m) (phi_iter_l m) (phiA_iterate_tA_of_prime m)
    (phiH_evE he M j lev v c m) hX

private def eLev (e : E.EtFam l K) (M : Model l K) (j lev : ℕ) : M.T j →+ M.MH lev j :=
  AddMonoidHom.mk' (fun x => e M lev j (x.lev lev)) fun x y => map_add (e M lev j) (x.lev lev) (y.lev lev)

private lemma natS {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] (n b : ℕ) (x : H) :
    (n ^ b : ℕ) • x = ((n : A) ^ b) • x := by
  exact (Nat.cast_smul_eq_nsmul A (n ^ b) x).symm.trans
    (congrArg (fun a : A => a • x) (Nat.cast_pow n b))

private lemma h1A {A : Type} [CommRing A] {TW H : Type 1} [AddCommGroup TW] [AddCommGroup H] [Module A H] (Ψ : TW →+ H)
    {d l s b : ℕ} (p : TW) (q : Fin d → TW) (p' : H) (q' : Fin d → H)
    (h : (l ^ b : ℕ) • p = (l ^ (s + b) : ℕ) • ∑ a, q a) (hp : Ψ p = p') (hq : ∀ a, Ψ (q a) = q' a) :
    ((l : A) ^ b) • p' = ((l : A) ^ (s + b)) • ∑ a, q' a := by
  have h' := congrArg Ψ h

  rw [map_nsmul, map_nsmul, map_sum, hp] at h'
  simp only [hq] at h'
  rw [natS (A := A), natS (A := A)] at h'
  exact h'

private lemma natE {e : E.EtFam l K} (he : e.Good) (W M : Model l K) (u : W.X ⟶ M.X) (hu : u ≫ M.p = W.p) (j lev : ℕ) (y : M.T j) :
    eLev e W j lev (Model.pullT u hu j y) = pullH (pxMap (okToOC l K) u hu) lev j (e M lev j (y.lev lev)) :=
  he.nat W M u hu lev j (y.lev lev)

private lemma h1L {e : E.EtFam l K} (he : e.Good) (W M : Model l K) (π : W.X ⟶ M.X) (hπ : π ≫ M.p = W.p) (j lev s b : ℕ)
    {d : ℕ} (τ : Fin d → (W.X ⟶ M.X)) (hτ : ∀ a, τ a ≫ M.p = W.p) (w y : M.T j)
    (h : (l ^ b : ℕ) • Model.pullT π hπ j w = (l ^ (s + b) : ℕ) • ∑ a, Model.pullT (τ a) (hτ a) j y) :
    ((l : Acris l) ^ b) • pullH (pxMap (okToOC l K) π hπ) lev j (e M lev j (w.lev lev)) =
      ((l : Acris l) ^ (s + b)) • ∑ a, pullH (pxMap (okToOC l K) (τ a) (hτ a)) lev j (e M lev j (y.lev lev)) := by
  exact h1A (A := Acris l) (H := MH W.P lev j) (eLev e W j lev) _ _ _ _ h (natE he W M π hπ j lev w)
    fun a => natE he W M (τ a) (hτ a) j lev y

private lemma finA {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] {Q : Type} [Fintype Q] (C : ℕ)
    (Ev : Q → H) (c : Q → A) (L tt κ : A) (hk : tt * κ = (C : A) * L)
    (h : C • (L • ∑ q, c q • Ev q) = 0) : tt • ∑ q, (κ * c q) • Ev q = 0 := by
  have e1 : ∑ q, (κ * c q) • Ev q = κ • ∑ q, c q • Ev q := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ => mul_smul _ _ _
  rw [e1, smul_smul, hk, mul_smul, Nat.cast_smul_eq_nsmul]
  exact h

private lemma cast_scale {A : Type} [CommRing A] (C l a b : ℕ) (t : A) :
    t * ((C * l ^ a * l ^ b : ℕ) : A) = (C : A) * ((l : A) ^ a * t * (l : A) ^ b) := by
  simp only [Nat.cast_mul, Nat.cast_pow]
  ring

private lemma levZero {e : E.EtFam l K} (he : e.Good) (M W : Model l K) (π : W.X ⟶ M.X) (hπ : π ≫ M.p = W.p)
    (j n f N0 N1 r s b a u C : ℕ) {d : Fin (n + 1) → ℕ} (τ : ∀ i, Fin (d i) → (W.X ⟶ M.X)) (hτ : ∀ i x, τ i x ≫ M.p = W.p)
    {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) (w : Fin (n + 1) → ι → M.T j) (σ : Fin (n + 1) → ℤ)
    (Y : ∀ lev, MH M.P lev j)
    (hAvg : ∀ lev (x : MH M.P lev j), pullH (pxMap (okToOC l K) π hπ) lev j x = 0 → C • x = 0)
    (h3 : ∀ lev, ∑ x : Σ i, Fin (d i), σ x.1 • pullH (pxMap (okToOC l K) (τ x.1 x.2) (hτ x.1 x.2)) lev j
      ((phiH M.P lev j)^[f * (n - x.1 + N0)] (Y lev)) = 0)
    (hX : ∀ lev, ((l : Acris l) ^ a * tA l ^ u) • evE e M j lev v (fun k => (phiA l)^[f * N1] (c k)) = tA l ^ (u + r) • Y lev)
    (hw2 : ∀ i k, (l ^ b : ℕ) • Model.pullT π hπ j (w i k) = (l ^ (s + b) : ℕ) • ∑ x, Model.pullT (τ i x) (hτ i x) j (v k))
    (lev : ℕ) :
    tA l ^ u • evE e M j lev (fun q : Fin (n + 1) × ι => w q.1 q.2)
      (fun q => ((C * l ^ (a + f * (n + N0) * u) * l ^ b : ℕ) : Acris l) *
        (((σ q.1 : ℤ) : Acris l) * (l : Acris l) ^ (f * (q.1 : ℕ) * r) * (phiA l)^[f * (n - q.1 + (N0 + N1))] (c q.2))) = 0 := by
  have h2 : ∀ i : Fin (n + 1), (((l : Acris l) ^ (a + f * (n + N0) * u) * tA l ^ u) * (l : Acris l) ^ (f * (i : ℕ) * r)) •
      evE e M j lev v (fun k => (phiA l)^[f * (n - i + (N0 + N1))] (c k)) =
      ((l : Acris l) ^ (f * (n + N0) * (u + r)) * tA l ^ (u + r)) • (phiH M.P lev j)^[f * (n - i + N0)] (Y lev) := by
    intro i
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.2
    have hM : f * (n - i + N0) + f * i = f * (n + N0) := by
      rw [← Nat.mul_add, Nat.add_right_comm, Nat.sub_add_cancel hi]
    have hI : (fun k => (phiA l)^[f * (n - i + (N0 + N1))] (c k)) = fun k => (phiA l)^[f * (n - i + N0)] ((phiA l)^[f * N1] (c k)) := by
      rw [← Nat.add_assoc, Nat.mul_add]
      exact funext fun k => Function.iterate_add_apply _ _ _ (c k)
    exact eqI he M j lev v (fun k => (phiA l)^[f * N1] (c k)) _ (Y lev) a u r (f * (n - i + N0)) (f * i) _ hM hI.symm (hX lev)
  let G : MH M.P lev j →ₗ[Acris l] MH W.P lev j := pullH (pxMap (okToOC l K) π hπ) lev j
  have S := UpperTheory.linear_combination_transfer_of_projector_relations (A := Acris l) (H := MH M.P lev j) (H' := MH W.P lev j) (J := Fin (n + 1)) (ι := ι) (I := fun i => Fin (d i))
    G (fun i x => pullH (pxMap (okToOC l K) (τ i x) (hτ i x)) lev j)
    (fun k => e M lev j ((v k).lev lev)) (fun i k => e M lev j ((w i k).lev lev))
    ((l : Acris l) ^ b) ((l : Acris l) ^ (s + b)) ((l : Acris l) ^ (a + f * (n + N0) * u) * tA l ^ u)
    ((l : Acris l) ^ (f * (n + N0) * (u + r)) * tA l ^ (u + r)) σ (fun i => (l : Acris l) ^ (f * (i : ℕ) * r))
    (fun i k => (phiA l)^[f * (n - i + (N0 + N1))] (c k)) (fun i => (phiH M.P lev j)^[f * (n - i + N0)] (Y lev))
    (fun i k => h1L he W M π hπ j lev s b (τ i) (hτ i) (w i k) (v k) (hw2 i k)) h2 (h3 lev)
  have A1 := hAvg lev _ ((G.map_smul _ _).trans S)
  exact finA (A := Acris l) (H := MH M.P lev j) C (fun q : Fin (n + 1) × ι => e M lev j ((w q.1 q.2).lev lev)) _
    (((l : Acris l) ^ (a + f * (n + N0) * u) * tA l ^ u) * (l : Acris l) ^ b) _ _ (cast_scale C l _ b _) A1

end UpperTheory.Ru.crystallineComparison

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison in

theorem UpperTheory.Ru.crystallineComparison.top : UpperTheory.Ru.crystallineComparison.Top := by
  intro l _ K _ _ ϖ hϖ e he M hsm hqc haff f n j hf T hr hPt A hA B hInj hAbs
  obtain ⟨m, N1, g, F, ρ, hg0, hgf, hF, hρ, hAI⟩ := hAbs
  refine (wEx l M.X (Fin (n + 1)) T).elim fun D => ?_
  have hl := UpperTheory.natCast_prime_ne_zero_and_not_isUnit_integers (l := l) (K := K)
  refine (wZero l f n (OK l K) ϖ hϖ hl.1 hl.2 M.X M.p hsm hqc haff hf T hr hPt
    (okToOC l K) g hg0 m F ρ hF hρ hgf D).elim fun N0 hZ => ?_
  refine (wTrans l (OK l K) M.X M.p (okToOC l K) (Fin (n + 1)) T D).elim fun gp hgp => ?_
  refine ⟨N0 + N1, fun x hx => ?_⟩
  refine (UpperTheory.exists_crystalline_lattice_expansion B M j x).elim fun ι h =>
    h.elim fun inst h => h.elim fun v h => h.elim fun c h => h.elim fun r hxvec => ?_
  let _ : Fintype ι := inst
  have hx' : IsInv B M j (vec B M j r v c) := hxvec ▸ hx
  refine (hAI ι v c r hx').elim fun a h => h.elim fun u h => h.elim fun X hX => ?_
  let W : Model l K := ⟨D.W, D.π ≫ M.p⟩
  refine (UpperTheory.hecke_correspondence_product M W D.π rfl j n T hr A hA D.s D.hs
    (fun i X y hy => D.gen X y hy i) v).elim fun s h => h.elim fun b h => h.elim fun w hw => ?_
  let σ : Fin (n + 1) → ℤ := fun i => (-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)
  have ha : (fun x : (Σ j : Fin (n + 1), Fin (T j).d) => (-1 : ℤ) ^ (x.1 : ℕ) * (((l ^ f) ^ ((x.1 : ℕ).choose 2) : ℕ) : ℤ)) = fun x => σ x.1 := by
    exact funext fun x => congrArg ((-1 : ℤ) ^ (x.1 : ℕ) * ·) (Nat.cast_pow (l ^ f) _)
  let τ (i : Fin (n + 1)) (k : Fin (T i).d) : W.X ⟶ M.X := D.s i k ≫ (T i).r
  have hτ (i : Fin (n + 1)) (k : Fin (T i).d) : τ i k ≫ M.p = W.p := by
    change (D.s i k ≫ (T i).r) ≫ M.p = D.π ≫ M.p
    rw [Category.assoc, hr, ← Category.assoc, D.hs]
  have hS := siteAnn l (OK l K) M.X M.p g W.P M.P ρ F f (Σ i : Fin (n + 1), Fin (T i).d)
    (fun x => σ x.1) (fun x => pxMap (okToOC l K) (τ x.1 x.2) (hτ x.1 x.2))
    (fun x => n - x.1 + N0) (ha ▸ hZ)
  let C := Fintype.card (∀ i, Equiv.Perm (Fin (T i).d))
  have hV := levZero he M W D.π rfl j n f N0 N1 r s b a u C τ hτ v c w σ
    (fun lev => pullH ρ lev j (X lev))
    (fun lev y hy => avgMH l W.P M.P (pxMap (okToOC l K) D.π rfl) _ gp hgp lev j y hy)
    (fun lev => hS lev j (X lev) (hX lev).1) (fun lev => (hX lev).2) hw.2
  have h0 := hInj (Fin (n + 1) × ι) (fun q => w q.1 q.2) _ u hV
  have hκ : C * l ^ (a + f * (n + N0) * u) * l ^ b ≠ 0 :=
    mul_ne_zero (mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  exact hxvec.symm ▸ UpperTheory.crystalline_expansion_relation_of_scaled_endomorphisms
    B M j f n (N0 + N1) r s _ hκ A v c w σ hw.1 h0
