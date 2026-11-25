module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.Twist GlobalTheory.CechPic

namespace GlobalTheory.Vert

section Chi

variable {X Y : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]

structure FiniteLenCoh (F : X.Modules) : Prop where

  ne_top : ∀ n, Module.length R (coh F n) ≠ ⊤

  eventually_zero : ∃ N, ∀ n, N ≤ n → Subsingleton (coh F n)

def chiLen (F : X.Modules) : ℤ := ∑ᶠ n, (-1 : ℤ) ^ n * (Module.length R (coh F n)).toNat

variable {F G : X.Modules} {S : ShortComplex X.Modules}

theorem chiLen_eq_of_linearEquiv [Algebra R Γ(Y, ⊤)] {H : Y.Modules}
    (e : ∀ n, coh F n ≃ₗ[R] coh H n) : chiLen R F = chiLen R H :=
  finsum_congr fun n => by rw [(e n).length_eq]

theorem chiLen_congr (e : F ≅ G) : chiLen R F = chiLen R G :=
  chiLen_eq_of_linearEquiv R fun n => cohOn.mapIso R ⊤ n e

end Chi

section Twists

variable {X Y : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]

def FiniteLenTwists (F : X.Modules) : Prop := ∀ M : LB X, M.IsLB → FiniteLenCoh R (twist F M)

def chiLenPic (F : X.Modules) : Pic X → ℤ :=
  Quotient.lift (fun M => chiLen R (twist F M.1)) fun M N h =>
    (Twist.nonempty_iso_of_lbIso M.2 N.2 h).elim (chiLen_congr R)

variable {F G : X.Modules} {M N : LB X} {S : ShortComplex X.Modules}

end Twists

section Sym

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

variable (G) in
abbrev SymQ : Type _ := SymmetricAlgebra ℚ (ℚ ⊗[ℤ] G)

def symOf : G →+ SymQ G :=
  (SymmetricAlgebra.ι ℚ _).toAddMonoidHom.comp (TensorProduct.mk ℤ ℚ G 1).toAddMonoidHom

theorem symOf_apply (g : G) : symOf g = SymmetricAlgebra.ι ℚ _ ((1 : ℚ) ⊗ₜ[ℤ] g) := rfl

def symLift {A : Type*} [CommRing A] [Algebra ℚ A] (f : G →+ A) : SymQ G →ₐ[ℚ] A :=
  SymmetricAlgebra.lift (LinearMap.liftBaseChange ℚ f.toIntLinearMap)

@[simp] theorem symLift_symOf {A : Type*} [CommRing A] [Algebra ℚ A] (f : G →+ A) (g : G) :
    symLift f (symOf g) = f g := by
  simp [symLift, symOf_apply]

def symMap (f : G →+ H) : SymQ G →ₐ[ℚ] SymQ H := symLift (symOf.comp f)

variable {φ ψ : G → ℤ} {d : ℕ}

theorem exists_topForm (h : DiffVanish (d + 1) φ) : ∃ l : SymQ G →ₗ[ℚ] ℚ,
    ∀ (ι : Type) [Fintype ι] (g : ι → G),
      l (∏ i, symOf (g i)) = if Fintype.card ι = d then ((multiDiff g φ 0 : ℤ) : ℚ) else 0 := by
  classical
  let f : Multiset G → ℚ := fun s =>
    if s.card = d then (shiftAct G ℤ (s.map diffElt).prod φ 0 : ℚ) else 0
  have hf (a b : G) (s : Multiset G) : f (s + {a + b}) = f (s + {a}) + f (s + {b}) := by
    simp only [f, Multiset.card_add, Multiset.card_singleton, Multiset.map_add (f := _),
      Multiset.map_singleton, Multiset.prod_add, Multiset.prod_singleton]
    split_ifs with hs
    · have : (s.map diffElt).prod * (diffElt a * diffElt b) ∈ diffIdeal G ^ (d + 1) := by
        rw [← hs, add_assoc, pow_add, pow_add, pow_one]
        refine Ideal.mul_mem_mul ?_ (Ideal.mul_mem_mul (diffElt_mem a) (diffElt_mem b))
        induction s using Quotient.inductionOn with
        | h s =>
          have := prod_diffElt_mem Finset.univ s.get
          rw [← List.prod_ofFn, ← Function.comp_def, ← List.map_ofFn, List.ofFn_get] at this
          simpa using this
      rw [diffElt_add, mul_sub, mul_add, map_sub, map_add (f := _), LinearMap.sub_apply,
        h.shiftAct_eq_zero this]
      simp
    · simp
  let l : MvPolynomial G ℚ →ₗ[ℚ] ℚ :=
    (MvPolynomial.basisMonomials G ℚ).constr ℚ fun m => f (Finsupp.toMultiset m)
  have hl (m : G →₀ ℕ) : l (MvPolynomial.monomial m 1) = f (Finsupp.toMultiset m) :=
    (MvPolynomial.basisMonomials G ℚ).constr_basis ℚ _ m
  let J : Ideal (MvPolynomial G ℚ) := Ideal.span (Set.range fun p : G × G =>
    MvPolynomial.X (p.1 + p.2) - (MvPolynomial.X p.1 + MvPolynomial.X p.2))
  have hJ : J.restrictScalars ℚ ≤ LinearMap.ker l := by
    intro x hx
    suffices ∀ r, l (r * x) = 0 by simpa using this 1
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      intro r
      induction r using MvPolynomial.induction_on' with
      | monomial m c =>
        rw [show MvPolynomial.monomial m c = c • MvPolynomial.monomial m (1 : ℚ) by
          simp [MvPolynomial.smul_monomial], smul_mul_assoc, map_smul]
        simp only [mul_sub, mul_add, map_sub, map_add (f := _), MvPolynomial.X,
          MvPolynomial.monomial_mul, mul_one, hl, Finsupp.toMultiset_single, one_nsmul, hf]
        simp
      | add p q hp hq => rw [add_mul, map_add (f := _), hp, hq, add_zero]
    | zero => simp
    | add x y _ _ hx hy => intro r; rw [mul_add, map_add (f := _), hx, hy, add_zero]
    | smul a x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc, hx]
  let c : G →+ MvPolynomial G ℚ ⧸ J := AddMonoidHom.mk' (fun g => Ideal.Quotient.mk J (.X g))
    fun a b => by
      rw [← map_add (f := _), Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨(a, b), rfl⟩
  refine ⟨(J.restrictScalars ℚ).liftQ l hJ ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℚ J).symm.toLinearMap ∘ₗ (symLift c).toLinearMap,
    fun ι _ g => ?_⟩
  have e : symLift c (∏ i, symOf (g i)) =
      Ideal.Quotient.mk J (MvPolynomial.monomial (∑ i, Finsupp.single (g i) 1) 1) := by
    rw [MvPolynomial.monomial_sum_one, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => symLift_symOf c _
  refine (congrArg (fun x => (J.restrictScalars ℚ).liftQ l hJ
    ((Submodule.Quotient.restrictScalarsEquiv ℚ J).symm x)) e).trans ((hl _).trans ?_)
  have e' : Finsupp.toMultiset (∑ i, Finsupp.single (g i) 1) = Finset.univ.val.map g := by

    simp only [map_sum, Finsupp.toMultiset_single, one_nsmul]
    rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Finset.univ.val.map g),
      Multiset.map_map]
    rfl
  simp only [f, e', Multiset.card_map, Multiset.map_map, multiDiff_eq_shiftAct]
  rfl

def topForm (h : DiffVanish (d + 1) φ) : SymQ G →ₗ[ℚ] ℚ := (exists_topForm h).choose

end Sym

section SmallPic

variable {X Y Z : Scheme.{0}}

instance small_pic : Small.{0} (Pic X) := by
  refine small_of_surjective (α := {p : Σ U : X → X.Opens, ∀ i j, Γ(X, U i ⊓ U j)ˣ //
    LB.IsLB ⟨X, p.1, p.2⟩}) (f := fun p => cls _ p.2) fun c => ?_
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  choose j hj using LB.mem_of_cover hL
  have h : LB.IsLB ⟨X, fun x => L.U (j x), fun x y => L.g (j x) (j y)⟩ :=
    ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hj x⟩, fun _ => hL.g_self _,
      fun _ _ _ => hL.cocycle _ _ _⟩
  exact ⟨⟨⟨_, _⟩, h⟩, (cls_eq_iff h hL).2
    (iso_of_chart hL ⟨j, fun _ => le_rfl, fun _ _ _ _ _ => rfl⟩)⟩

variable (X) in
abbrev SmallPic : Type := Shrink.{0} (Pic X)

variable (X) in
def smallPicEquiv : SmallPic X ≃+ Pic X := Shrink.addEquiv

def smallCls (L : LB X) (hL : L.IsLB) : SmallPic X := (smallPicEquiv X).symm (cls L hL)

def smallPull (f : Y ⟶ X) : SmallPic X →+ SmallPic Y :=
  (smallPicEquiv Y).symm.toAddMonoidHom.comp ((pull f).comp (smallPicEquiv X).toAddMonoidHom)

variable (X) in
abbrev PicSym : Type := SymQ (SmallPic X)

def c1 (L : LB X) (hL : L.IsLB) : PicSym X := symOf (smallCls L hL)

variable {d : ℕ} {φ ψ : Pic X → ℤ}

def picForm (h : DiffVanish (d + 1) φ) : PicSym X →ₗ[ℚ] ℚ :=
  topForm (h.comap (smallPicEquiv X).toAddMonoidHom)

end SmallPic

end GlobalTheory.Vert
