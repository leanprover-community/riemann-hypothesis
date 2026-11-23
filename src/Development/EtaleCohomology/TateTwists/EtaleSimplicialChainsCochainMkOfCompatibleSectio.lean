module

public import Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainExistsFromNaturalSections
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MkPf

variable {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}

noncomputable def eta (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (freeP R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ (I.X s).obj where
  app U := ModuleCat.freeDesc (R := ULift.{1} R) (X := ULift.{1} (Sx E p U.unop))
    (M := (I.X s).obj.obj U) (TypeCat.ofHom fun (y : ULift.{1} (Sx E p U.unop)) => a p s h U.unop y.down)
  naturality U V f := by
    refine ModuleCat.free_hom_ext (X := ULift.{1} (Sx E p U.unop)) (fun y => ?_)
    have := ha p s h V.unop U.unop f.unop y.down
    simp only [Sec.res, Sx.res, Quiver.Hom.op_unop] at this
    change (ModuleCat.freeDesc (M := (I.X s).obj.obj V)
        (TypeCat.ofHom fun (z : ULift.{1} (Sx E p V.unop)) => a p s h V.unop z.down))
        ((ModuleCat.free (ULift.{1} R)).map (TypeCat.ofHom fun (z : ULift.{1} (Sx E p U.unop)) =>
          ULift.up.{1} ((E.obj (op (SimplexCategory.mk p))).map f z.down)) (ModuleCat.freeMk y)) =
      ((I.X s).obj.map f) (ModuleCat.freeDesc (M := (I.X s).obj.obj U)
        (TypeCat.ofHom fun (z : ULift.{1} (Sx E p U.unop)) => a p s h U.unop z.down) (ModuleCat.freeMk y))
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact this.symm

noncomputable def mF (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ (I.X s)).symm
    (eta a ha p s h)

lemma mF_gen (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ((mF a ha p s h).hom.app (op U)).hom (freeGen R _ U x) = a p s h U x := by
  have e := toSheafify_sheafifyLift Scheme.etaleTopology.{0} (eta a ha p s h) (I.X s).property
  have e2 := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) e
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e2
  exact e2.trans (ModuleCat.freeDesc_apply _ _)

noncomputable def mC (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    Cochain ((chains R).obj E) I n :=
  Cochain.mk fun i j hij => if hi : i ≤ 0 then
    (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫
      (chainsXIso R E (-i).toNat).hom ≫ mF a ha (-i).toNat j (by omega)
  else 0

lemma mC_v (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) :
    (mC a ha).v _ _ h = (chainsXIso R E p).hom ≫ mF a ha p s h := by
  have key : ∀ (q : ℕ), q = p → ∀ (e : -(p : ℤ) = -(q : ℤ)) (h' : -(q : ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ (chainsXIso R E q).hom ≫ mF a ha q s h' =
        (chainsXIso R E p).hom ≫ mF a ha p s h := by
    rintro q rfl e h'
    simp
  rw [mC, Cochain.mk_v, dite_eq_left (by omega)]
  exact key _ (by omega) _ _

end LateralTheory.EtaleFoundations.MkPf

open LateralTheory.EtaleFoundations LateralTheory.EtaleFoundations.MkPf in
theorem LateralTheory.EtaleFoundations.etale_simplicial_chains_cochain_mk_of_compatible_sections : EtaleSimplicialCochainExistsFromNaturalSections := by
  intro R _ E I n a ha
  refine ⟨mC a ha, fun p s h U x => ?_⟩
  unfold ev
  rw [mC_v, Iso.inv_hom_id_assoc]
  exact mF_gen a ha p s h U x
