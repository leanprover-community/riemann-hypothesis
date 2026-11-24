module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPreservedUnitaryLatticeChanges
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteDatum_level_preserved_unitary_lattice_changes : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : HomE D.host.E a b → ℂ) (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → DatLoc D cc SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) → DatLoc D cc SS cl N N' Ξ := by
  first | exact @GlobalTheory.TwV.datLoc_of_move | exact GlobalTheory.TwV.datLoc_of_move | (intros; apply GlobalTheory.TwV.datLoc_of_move <;> assumption)
