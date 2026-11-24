module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem iso_directSum_fockOne : ∀ (a b : ℕ) (α β : ℤ), Iso (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b))) ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) (fockOne a b α β) := by
  intro a b α β
  obtain ⟨e⟩ := GlobalTheory.GLDuality.nonempty_equiv_polyRep a b
  obtain ⟨e, he⟩ := Iso.of_equiv e
  refine ⟨e, fun p x => ?_⟩
  have key : (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod
      ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b)))
      ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) p x =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
      (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) =>
        GlobalTheory.GLDuality.pieceRep (MonoidHom.id (GL (Fin a) ℂ)) (MonoidHom.id (GL (Fin b) ℂ)) i)
        (unitaryIncl a (conjU a p.1), unitaryIncl b p.2) x := by
    apply DFinsupp.ext
    intro i
    change TensorProduct.map ((((detU a ^ α) p.1 : ℂˣ) : ℂ) • (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)))
        ((((detU b ^ β) p.2 : ℂˣ) : ℂ) • (irr b (GlobalTheory.GLDuality.pad b i) p.2)) (x i) =
      ((((detU a ^ α) p.1 * (detU b ^ β) p.2 : ℂˣ) : ℂ)) •
        TensorProduct.map (irr a (GlobalTheory.GLDuality.pad a i) (conjU a p.1)) (irr b (GlobalTheory.GLDuality.pad b i) p.2) (x i)
    rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul, Units.val_mul, LinearMap.smul_apply]
  rw [key, map_smul, he]
  rfl

end GlobalTheory.OneFunctional
