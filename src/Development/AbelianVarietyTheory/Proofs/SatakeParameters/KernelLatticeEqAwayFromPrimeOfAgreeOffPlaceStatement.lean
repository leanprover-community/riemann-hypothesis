module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeEqAwayFromPrimeOfAgreeOffPlace
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.kernelLattice_eq_away_from_prime_of_agree_off_place : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (n p : ℕ) [Fact p.Prime] (G : GAtP p) (A : LocAt D.host.F D.host.E n G), LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf p (G.P.W v) (A.iw v) P → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (a : 𝓞 D.host.E) (Lb : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin N → D.host.E)) = ⊤ → ∀ x x' : GL (Fin N) (AfE D.host.F D.host.E), SameOff (A.pl v).1 x x' → GL3Theta.EqOff D P (latK D.sp J a x Lb) (latK D.sp J a x' Lb) := by
  first | exact @GlobalTheory.TwV.Xc.eqOff_latK_of_sameOff | exact GlobalTheory.TwV.Xc.eqOff_latK_of_sameOff | (intros; apply GlobalTheory.TwV.Xc.eqOff_latK_of_sameOff <;> assumption)
