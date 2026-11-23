module

public import Formalism.LocalToGlobal.HermitianColumns.SymAll
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeUOperatorRationalInvertibleRamifiedForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.heckeUOperator_rational_invertible_ramifiedForms : ∀ (X : Stages), Nonempty (PreX X.B.toPre) → ∀ (H : Formalism.L2.Herm.ColsHermS X.toD7) (T : ∀ u, Formalism.L2.Forms.Forms0 X.toD7 u), (∀ u, Formalism.L2.Forms.Joint0 H.base.lev0 u (T u)) → (∀ u i v h x, ∃ r : X.B.LL, X.B.embLL r = (T u).gl.psi0 i v h x) → ∀ u (w : X.toD7.what₂.places.Pl), X.toD7.what₂.places.resChar w = (X.toD7.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL X.toD7 u, X.toD7.nuIn u (n • x) ∈ LT.Nlam X.toD7 u w) ∧ ∀ x, X.toD7.nuIn u x ∈ LT.Nlam X.toD7 u w → InLoc (X.toD7.plEq w) (DV.MramL X.toD7 u) (n • x) := by
  first | exact @GlobalTheory.LevelHecke.commensurable_at_level | exact GlobalTheory.LevelHecke.commensurable_at_level | (intros; apply GlobalTheory.LevelHecke.commensurable_at_level <;> assumption)
