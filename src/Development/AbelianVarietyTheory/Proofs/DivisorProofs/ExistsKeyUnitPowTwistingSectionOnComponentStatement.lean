module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyUnitPowTwistingSectionOnComponent
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

theorem _root_.GlobalTheory.T.exists_keyUnit_pow_twistingSection_on_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ (Z : Comp Xo c) (m : ℕ), ∃ t : GlobalTheory.FlatTw.TwSec U x Z (wtOf Dw 0 (-(4 * (m : ℤ)))), (∀ w, 0 ≤ t.lo w) ∧ ∀ σ, Real.log (t.cInf σ) ≤ (m : ℝ) * (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) := by
  first | exact @GlobalTheory.KeyPowTw.exists_twSec_keyPow | exact GlobalTheory.KeyPowTw.exists_twSec_keyPow | (intros; apply GlobalTheory.KeyPowTw.exists_twSec_keyPow <;> assumption)
