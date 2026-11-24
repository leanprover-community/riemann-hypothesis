module

public import Development.EtaleCohomology.TateTwists.EtaleCochainExistsOfNaturalEvaluation
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable (R : Type) [CommRing R]

noncomputable def psiOf (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift.{1} (P.obj U) => a U.unop x.down)
  naturality := by
    intro U V g
    refine ModuleCat.free_hom_ext (fun x => ?_)
    have := ha V.unop U.unop g.unop x.down
    simp [freeP] at this ⊢
    exact this.symm

theorem free_hom_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let ψ := psiOf R P F a ha
  let φ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj ((freeP R).obj P) ⟶ F :=
    ((sheafificationAdjunction _ _).homEquiv _ _).symm ψ
  have key : toSheafify _ ((freeP R).obj P) ≫ φ.hom = ψ := by
    have := ((sheafificationAdjunction _ _).homEquiv _ _).apply_symm_apply ψ
    rw [Adjunction.homEquiv_unit] at this
    exact this
  refine ⟨φ, fun U x => ?_⟩
  change ((toSheafify _ ((freeP R).obj P)).app (op U) ≫ φ.hom.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = _
  rw [← NatTrans.comp_app, key]
  erw [ModuleCat.freeDesc_apply]
  rfl

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  intro R _ E I n a ha
  have hex : ∀ (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s), ∃ φ : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s,
      ∀ U x, Sec.map φ (freeGen R _ U x) = a p s h U x :=
    fun p s h => free_hom_exists R _ _ (a p s h) (fun V U g x => ha p s h V U g x)
  choose φ hφ using hex
  let f : ∀ (p : ℕ) (s : ℤ) (_ : -(p:ℤ) + n = s), (((chains R).obj E).X (-(p:ℤ)) ⟶ I.X s) :=
    fun p s h => (chainsXIso R E p).hom ≫ φ p s h
  let α : Cochain ((chains R).obj E) I n := Cochain.mk (fun i j hij =>
    if hi : 0 ≤ -i then
      (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫ f (-i).toNat j (by omega)
    else 0)
  refine ⟨α, fun p s h U x => ?_⟩
  have gen : ∀ (q : ℕ) (hq : q = p) (e : -(p:ℤ) = -(q:ℤ)) (h' : -(q:ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ f q s h' = f p s h := by
    rintro q rfl e h'
    simp
  have hv : α.v (-(p:ℤ)) s h = f p s h := by
    simp only [α, Cochain.mk_v]
    rw [dite_eq_left (by omega)]
    exact gen _ (by omega) _ _
  simp only [GlobalTheory.EtC.ev]
  rw [hv]
  simp only [f]
  rw [Iso.inv_hom_id_assoc]
  exact hφ p s h U x
