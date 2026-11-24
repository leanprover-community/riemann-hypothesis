module

public import Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductOfFamilyAndLeibniz
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistCupPairingOfTensorAndResolutionPro
public import Development.EtaleCohomology.TateTwists.TensorLocallyBijectiveHolds
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductLeibnizOfSeparated, Development.EtaleCohomology.TateTwists.TwpairTensUnivPf

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductLeibnizOfSeparated =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductLeibnizOfSeparated", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductOfFamilyAndLeibniz\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

def SecSep : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U),
    (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b

lemma res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  exact congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op).symm

lemma res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ x y

lemma res_usmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (x : Sec F U) :
    Sec.res g (u • x) = u • Sec.res g x := by
  simp only [Units.smul_def]; exact map_zsmul _ _ x

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hP V g hg)⟩

lemma leib_lift {R : Type} [CommRing R] {I J K T M L : Cx R} (τ : Pair I J T) (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U)
    (heq : ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c))
    (V : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (x : Tens I J V s) (b : Sec (K.X t) V) :
    Sec.map (L.d w (w + 1)) (m V s t w h (τ.lift V s x) b) = m V (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) (τ.lift V s x)) b +
          s.negOnePow • m V s (t + 1) (w + 1) (by omega) (τ.lift V s x) (Sec.map (K.d t (t + 1)) b) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
    rw [hx, hy]; abel
  | of p z =>
    obtain ⟨⟨s1, t1⟩, hp⟩ := p
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add (f := _), LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
      rw [hx, hy]; abel
    | tmul a1 b1 =>
      have hl : τ.lift V s (DirectSum.of _ ⟨(s1, t1), hp⟩ (a1 ⊗ₜ b1)) = τ.mul V s1 t1 s hp a1 b1 := by
        unfold Pair.lift
        rw [← DirectSum.lof_eq_of (ULift.{1} R), DirectSum.toModule_lof, TensorProduct.lift.tmul]
      simp only at hp
      rw [hl, τ.leibniz V s1 t1 s hp a1 b1]
      rw [heq V s1 t1 t s (t1 + t) w hp h (by omega) (by omega)]
      rw [ν'.leibniz V s1 (t1 + t) w (by omega), μ'.leibniz V t1 t (t1 + t) rfl]
      simp only [map_add (f := _), LinearMap.add_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]
      rw [heq V (s1 + 1) t1 t (s + 1) (t1 + t) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 (t1 + 1) t (s + 1) (t1 + t + 1) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 t1 (t + 1) s (t1 + t + 1) (w + 1) hp (by omega) (by omega) (by omega)]
      have hs : ((s.negOnePow : ℤˣ) : ℤ) = (s1.negOnePow : ℤ) * (t1.negOnePow : ℤ) := by
        rw [← Units.val_mul, ← Int.negOnePow_add, hp]
      rw [hs, mul_smul, smul_add]
      abel

end LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

open LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated in
theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_leibniz_of_separated (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) :
    LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz := by
  intro R _ I J K T τ hτ M L μ' ν' m hnat heq U s t w h a b
  apply hsep R (L.X (w + 1)) U
  refine loc_mono (hτ.1 U s a) ?_
  rintro V g ⟨x, hx⟩
  rw [res_map, hnat, res_add, res_usmul, hnat, hnat, res_map, res_map, ← hx, leib_lift τ μ' ν' m heq]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductLeibnizOfSeparated =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.TwpairTensUnivPf =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.TwpairTensUnivPf", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleTateTwistCupPairingOfTensorAndResolutionPro\npublic import Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductLeibnizOfSeparated\npublic import Development.EtaleCohomology.TateTwists.TensorLocallyBijectiveHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem secmap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := rfl

noncomputable def pairPost {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    rw [← μ.nat g s t w h a b]
    exact _root_.LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.res_map (u.f w) g _
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    have hc : Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) =
        Sec.map (u.f (w + 1)) (Sec.map (K.d w (w + 1)) (μ.mul U s t w h a b)) := by
      rw [secmap_comp, secmap_comp, u.comm]
    show Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = _
    rw [hc, μ.leibniz U s t w h a b]
    show Sec.map (u.f (w + 1)) _ = Sec.map (u.f (w + 1)) _ + _ • Sec.map (u.f (w + 1)) _
    rw [Sec.map, map_add (f := _), map_zsmul_unit]

def twpair_tens_univ_uniq : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K'), τ.Compat ν f g u → τ.Compat ν f g u' → u = u'

def twpair_tens_univ_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃ u : K ⟶ K', τ.Compat ν f g u

def twpair_tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0

theorem pairPost_compat {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') :
    μ.Compat (pairPost μ u) (𝟙 I) (𝟙 J) u := by
  intro U s t w h a b
  rfl

theorem lift_comp_eq {R : Type} [CommRing R] {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K')
    (hu : τ.Compat ν f g u) (hu' : τ.Compat ν f g u') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) :
    Sec.map (u.f w) (τ.lift V w x) = Sec.map (u'.f w) (τ.lift V w x) := by
  classical
  have key : ((u.f w).hom.app (op V)).hom ∘ₗ τ.lift V w = ((u'.f w).hom.app (op V)).hom ∘ₗ τ.lift V w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (hu V _ _ _ p.2 a b).trans (hu' V _ _ _ p.2 a b).symm
  exact congrArg (fun k => k x) key

theorem tens_univ_uniq_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_uniq := by
  intro R _ I J K τ hτ I' J' K' ν f g u u' hu hu'
  ext w U y
  apply hsep R (K'.X w) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop w y) ?_
  rintro V r ⟨x, hx⟩
  rw [_root_.LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.res_map, _root_.LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.res_map, ← hx]
  exact lift_comp_eq τ ν f g u u' hu hu' V w x

theorem sec_zero_of_isZero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [h]
  exact this

theorem isZero_of_sec {R : Type} [CommRing R] {F : Shv R} (h : ∀ (U : Scheme.{0}) (x : Sec F U), x = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact (h U.unop y).trans (h U.unop _).symm

theorem tens_univ_ge_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_ge := by
  intro R _ I J K τ hτ hI hJ
  have hK : ∀ w : ℤ, w < 0 → IsZero (K.X w) := by
    intro w hw
    apply isZero_of_sec
    intro U y
    apply hsep R (K.X w) U
    refine TensLocbij.loc_mono (hτ.1 U w y) ?_
    rintro V r ⟨x, hx⟩
    rw [← hx]
    classical
    have hl : τ.lift V w = 0 := by
      apply DirectSum.linearMap_ext
      intro p
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.zero_apply]
      rcases lt_or_ge p.1.1 0 with hs | hs
      · rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE I 0 p.1.1 hs) a, map_zero, LinearMap.zero_apply]
      · have ht : p.1.2 < 0 := by have := p.2; omega
        rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE J 0 p.1.2 ht) b, map_zero]
    rw [hl, LinearMap.zero_apply]
    exact (map_zero _).symm
  exact ⟨fun i hi => hK i ((ComplexShape.notMem_range_embeddingUpIntGE_iff (p := 0) i).1 hi)⟩

theorem etale_sheaf_sections_separated_holds : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep := by
  intro R _ F U a b hab
  obtain ⟨S, hS, hP⟩ := hab
  have h1 : Presheaf.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property
  have h2 := (isSheaf_iff_isSheaf_of_type _ _).1 h1
  exact (h2 S hS).isSeparatedFor.ext fun V g hg => hP V g hg

def twpair_tens_univ_exdeg : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ), ∃ φ : K.X w ⟶ K'.X w, ∀ (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map φ (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

theorem tens_univ_ex_of (hdeg : twpair_tens_univ_exdeg) : twpair_tens_univ_ex := by
  intro R _ I J K τ hτ I' J' K' ν f g
  choose φ hφ using hdeg R τ hτ ν f g
  have hsep := etale_sheaf_sections_separated_holds
  refine ⟨⟨φ, ?_⟩, fun U s t w h a b => hφ w U s t h a b⟩
  rintro i j (hij : i + 1 = j)
  subst hij
  ext U y
  apply hsep R (K'.X (i + 1)) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop i y) ?_
  rintro V r ⟨x, hx⟩
  show Sec.res r (Sec.map (φ i ≫ K'.d i (i + 1)) y) = Sec.res r (Sec.map (K.d i (i + 1) ≫ φ (i + 1)) y)
  rw [_root_.LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.res_map, _root_.LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.res_map, ← hx]
  classical
  have key : ((K.d i (i + 1) ≫ φ (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i =
      ((φ i ≫ K'.d i (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e1 : Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (φ (i + 1)) (Sec.map (K.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    have e2 : Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (K'.d i (i + 1)) (Sec.map (φ i) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    change Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) = Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)
    have h1 := hφ (i + 1) V (p.1.1 + 1) p.1.2 (by have := p.2; omega) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) b
    have h2 := hφ (i + 1) V p.1.1 (p.1.2 + 1) (by have := p.2; omega) a (Sec.map (J.d p.1.2 (p.1.2 + 1)) b)
    have hf : Sec.map (I'.d p.1.1 (p.1.1 + 1)) (Sec.map (f.f p.1.1) a) = Sec.map (f.f (p.1.1 + 1)) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) := by
      rw [secmap_comp, secmap_comp, f.comm]
    have hg : Sec.map (J'.d p.1.2 (p.1.2 + 1)) (Sec.map (g.f p.1.2) b) = Sec.map (g.f (p.1.2 + 1)) (Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
      rw [secmap_comp, secmap_comp, g.comm]
    rw [e1, e2, τ.leibniz, hφ i, ν.leibniz, hf, hg]
    simp only [Sec.map, map_add (f := _), map_zsmul_unit] at h1 h2 ⊢
    rw [h1, h2]
  exact (congrArg (fun k => k x) key).symm

theorem twpair_tens_univ_of (hdeg : twpair_tens_univ_exdeg) :
    LateralTheory.EtaleFoundations.twpair_tens_univ := by
  have hsep := etale_sheaf_sections_separated_holds
  have hex := tens_univ_ex_of hdeg
  intro R _ I J K τ hτ
  refine ⟨?_, tens_univ_ge_of hsep R τ hτ, fun u => ⟨pairPost τ u, pairPost_compat τ u⟩⟩
  intro I' J' K' ν f g
  obtain ⟨u, hu⟩ := hex R τ hτ ν f g
  exact ⟨u, hu, fun u' hu' => tens_univ_uniq_of hsep R τ hτ ν f g u' u hu' hu⟩

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.TwpairTensUnivPf =====
