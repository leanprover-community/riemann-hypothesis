module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BlockGLMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankTwo
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankZero
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaSuccOfForall
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Pbf

private theorem functor_to_single_object_const {G : Type} [Monoid G] {n : ℕ} (y : Fin 1 ⥤ SingleObj G) (θ : Fin (n + 1) ⥤ Fin 1) :
    θ ⋙ y = (Functor.const _).obj (SingleObj.star G) := by
  have key : ∀ (a b : Fin 1) (g : a ⟶ b), y.map g = 𝟙 _ := by
    intro a b g
    obtain rfl : a = b := Subsingleton.elim _ _
    rw [Subsingleton.elim g (𝟙 a), y.map_id]
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  simp only [Functor.comp_map, Functor.const_obj_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact key _ _ _

private theorem eq_triv (U : Scheme.{0}) {N : ℕ} (V : sch.obj U ⟶ ofCat (glCat N)) : V = triv (sch.obj U) N := by
  ext k T x
  let f : (Opposite.op (SimplexCategory.mk 0)) ⟶ k := (SimplexCategory.isTerminalZero.from k.unop).op
  have h := congrArg (fun φ => (ConcreteCategory.hom (NatTrans.app φ T)).toFun x) (V.naturality f)
  refine h.trans ?_
  exact functor_to_single_object_const _ _

private theorem pbf_all (q : ℕ) [NeZero q] (N : ℕ) : ∀ E : Spc, Inv q E → PBF q E N := by
  induction N with
  | zero => exact fun E _ => UpperTheory.projectiveBundleFormula_rank_zero q E
  | succ N ih =>
    rcases N with _ | _ | N
    · exact UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q
    · exact UpperTheory.projectiveBundleFormula_rank_two q
    · exact UpperTheory.projectiveBundleFormula_succ_of_forall q (N + 2) (by omega) ih

end UpperTheory.Pbf

theorem UpperTheory.Cb.etaleCohomology_projectiveBundle_formula :
    ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), ∀ {N : ℕ} (V : sch.obj U ⟶ ofCat (glCat N)), Inv q (sch.obj U) → ∀ n i : ℤ, Function.Bijective fun a : ∀ j : Fin N, Ht q (sch.obj U) (n - 2 * (j : ℕ)) (i - (j : ℕ)) => ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j)) (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i) := by
  intro q _ U N V h n i
  obtain rfl := UpperTheory.Pbf.eq_triv U V
  exact UpperTheory.Pbf.pbf_all q N _ h n i
