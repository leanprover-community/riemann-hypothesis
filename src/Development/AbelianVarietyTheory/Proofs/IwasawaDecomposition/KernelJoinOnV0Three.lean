module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqIntegralOfAe
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.KernelJoin

theorem heq_of_reindex {K W Mem : Type} [Field K] (a : Mem → ℕ) {V : W → Type} [∀ u, AddCommGroup (V u)]
    [∀ u, Module K (V u)] {Z : Mem → Type} {Y : W → Type} (b : ∀ x, Fin (a x) → Z x) (g : ∀ u, V u → Y u)
    (w w' : W → Mem) (ν : ∀ u, (Fin (a (w u)) → K) ≃ₗ[K] V u) (ν' : ∀ u, (Fin (a (w' u)) → K) ≃ₗ[K] V u)
    (hw : w = w') (hν : HEq ν ν') (h : ∀ u i, HEq (b (w' u) i) (g u (ν' u (Pi.single i 1)))) :
    ∀ u i, HEq (b (w u) i) (g u (ν u (Pi.single i 1))) := by
  subst hw
  cases hν
  exact h

theorem smul_apply_eq_of_eq {A B : Type} [AddCommGroup B] [Module ℂ B] (f : A → B) {a a' : A} (h : a = a')
    (k κ : ℂ) {b : B} (hb : f a' = κ • b) : k • f a = (k * κ) • b := by
  rw [h, hb, mul_smul]

end GlobalTheory.Mem.SJ.KernelJoin
