module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.TwQThetaOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTwistLevelContainsPrincipalCongruence
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStep_twist_level_contains_principal_congruence : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι), ∃ N : I.Q a → ℕ, (∀ P : I.Q a, P.1.valuation B.host.E (((qOf P.1 : ℕ) : B.host.E) ^ (topDep B.R (I.cst a).M + 1)) ≤ WithZero.exp (-(N P : ℤ))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m)) → ∃ h : g ∈ ((I.Tp a).levQ B.R.m P).H, ((I.Tp a).levQ B.R.m P).lam ⟨g, h⟩ = 1 := by
  exact @GlobalTheory.Mem.Col2.TC.levQ_top_princ
