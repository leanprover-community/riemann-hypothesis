module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceCompactTorusClassesCompactWeylCosets
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

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.real_place_compact_torus_classes_compactWeyl_cosets : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau), CompactSpace (Tor P (placeOf D ρ).Completion) → ∀ WK : Subgroup (Equiv.Perm (Fin V.rank)), (∀ w, w ∈ WK ↔ w ∈ GlobalTheory.HCChar.compactWeyl (M.ε ρ)) → ∃ (T : Finset (Equiv.Perm (Fin V.rank))) (b : XSet P (placeOf D ρ).Completion V.gram ≃ T), Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin V.rank)))⁻¹ * (p.1 : Equiv.Perm (Fin V.rank))) ∧ ∀ (q : XSet P (placeOf D ρ).Completion V.gram) (γ : GArch D.sp.cm.sig V.gram (placeOf D ρ)), HasCls P (placeOf D ρ).Completion V.gram γ q.1 → ∃ g, GlobalTheory.Orb.frameMat M ρ (g * γ * g⁻¹) = Matrix.diagonal fun i => cxRoots (embOverOf D ρ).1 P ((b q : Equiv.Perm (Fin V.rank))⁻¹ i) := by
  first | exact @GlobalTheory.TrEll.RealClasses.real_classes | exact GlobalTheory.TrEll.RealClasses.real_classes | (intros; apply GlobalTheory.TrEll.RealClasses.real_classes <;> assumption)
