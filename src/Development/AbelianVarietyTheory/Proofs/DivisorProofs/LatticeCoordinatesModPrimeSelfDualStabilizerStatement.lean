module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinatesModPrimeSelfDualStabilizer
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ PP : Formalism.L2.DIV.Pl D.host.E, ∃ φ : La →ₗ[𝓞 D.host.E] (Fin V.rank → kP PP), Function.Surjective φ ∧ ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ M : ℕ, (M : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ a b : La, (∃ w ∈ latGHat V 1, finVec V (ι b) - (finHom V k).1.mulVec (finVec V (ι a)) = M • w) → φ b = (redFn β PP (Lev.finE V k)).1.mulVec (φ a) := by
  first | exact @GlobalTheory.LatCoordRed.coord_red | exact GlobalTheory.LatCoordRed.coord_red | (intros; apply GlobalTheory.LatCoordRed.coord_red <;> assumption)
