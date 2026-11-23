module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.AdmissibleDesigns.AdmG5OfAdm51AdmG5
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkTameShape

theorem splitL_diagonal {K : Type} [Field K] (a b n : ℕ) (hn : n = a + b) (c : K) (y : Fin n → K) :
    Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn ((Matrix.diagonal fun k : Fin n => if (k : ℕ) < a then 1 else c).mulVec y) =
      ((Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn y).1, c • (Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL a b n hn y).2) := by
  ext j
  · simp [Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]
  · simp [Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL, Matrix.mulVec_diagonal]

theorem rhoBarTw_eq (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (a : ℤ) : rhoBarTw D.nd ρ π a =
      twistRep (glRep (redRep D.nd i (ρ π))) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i a) := by
  have hz : ∀ (u : (D.nd.O i)ˣ) (n : ℤ), IsLocalRing.residue (D.nd.O i) ((u ^ n : (D.nd.O i)ˣ) : D.nd.O i) =
      (IsLocalRing.residue (D.nd.O i) u) ^ n := by
    intro u n
    have := congrArg Units.val (map_zpow (Units.map (IsLocalRing.residue (D.nd.O i)).toMonoidHom) u n)
    rw [Units.val_zpow_eq_zpow_val] at this
    simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using this
  have hs : ∀ (c : D.nd.O i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)),
      (c • M).map (IsLocalRing.residue (D.nd.O i)) =
        IsLocalRing.residue (D.nd.O i) c • M.map (IsLocalRing.residue (D.nd.O i)) := fun c M => by
    ext; simp
  refine MonoidHom.ext fun g => LinearMap.ext fun u => funext fun k => ?_
  simp [rhoBarTw, twistRep, glRep, matRep, mapM, twistM, redRep, mapRep, Formalism.MainNotions.SumRepresentations.At.chiEpsBar, rhoO]
  rw [hs, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hz, map_units_inv]

end GlobalTheory.NLinkTameShape

end
