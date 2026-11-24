module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainDegreeZeroSubsingleton
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.bnat : ∀ {R : Type} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M] (N : SingleObj (Multiplicative ℕ) ⥤ ModuleCat.{w} R) (a : M →ₗ[R] N.obj (SingleObj.star _)) (s : R), (∀ x, (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd 1)).hom (a x) = a x) → Acyc1 s a (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd 1)).hom → (cx N).ResUpTo s (aug N fun _ => a) := fun N a s h H =>
  GlobalTheory.CompanionTheory.NatCoh.resUpTo_of_acyc N a s h H.1 (fun y hy => H.2.1 y (sub_eq_zero.1 hy)) H.2.2
