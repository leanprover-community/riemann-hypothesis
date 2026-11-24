module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrimeUnderFirstFactorAtPlaceOverP
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
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.exists_prime_under_firstFactor_at_placeOverP : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n p : ℕ) [Fact p.Prime] (G : GAtP p) (A : LocAt F E n G), LocInt A → SplAlg A → ∀ v, ∃ P : HeightOneSpectrum (𝓞 E), PrimeOf p (G.P.W v) (A.iw v) P ∧ (∀ (y : G.P.W v) (k : ℕ), ∃ (x : 𝓞 E) (z : G.P.W v), A.iw v x = algebraMap _ _ (y + (p : G.P.W v) ^ k * z)) ∧ ((p : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  first | exact @GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place | exact GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place | (intros; apply GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place <;> assumption)
