module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImaginaryLatticeScalingIndex
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

@[expose] public section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

theorem _root_.GlobalTheory.T.imaginary_lattice_scaling_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), Unr E → 1 ≤ r → (AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E)).relIndex (imLat E) = r ^ fdeg E := by
  first | exact @GlobalTheory.LieDisc.relIndex_mulLeft_imLat | exact GlobalTheory.LieDisc.relIndex_mulLeft_imLat | (intros; apply GlobalTheory.LieDisc.relIndex_mulLeft_imLat <;> assumption)
