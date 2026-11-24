module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistedTriples
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRhoOfRowOfFrobeniusEigenvalues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG


theorem _root_.GlobalTheory.T.isRhoOfRow_of_frobenius_eigenvalues : ∀ (D : D7) (Rw : RowSide D) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT), GlobalTheory.HeightCounting.RhoSpec D Rw rowS → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (s : D.ntw.Sig (D.ntw.twOf a)), GlobalTheory.RowTriple.ReadTw D a → D.ntw.side _ s = D.ntw.twSide a → D.ntw.jS _ s = D.nd.j a → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsGoodRow D a σ → (∀ w, IsSplitPl D.host w → D.naut.locW a σ w = Rw.locR σ w) → (∀ᶠ P in Filter.cofinite, IsSplitPl D.host P → D.naut.frobEig (Rw.locR (rowS _ s) P) = D.naut.frobEig (Rw.locR σ P)) → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsRhoOfRow D a σ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) := by
  first | exact @GlobalTheory.TripRho.isRhoOfRow_of_frobEig | exact GlobalTheory.TripRho.isRhoOfRow_of_frobEig | (intros; apply GlobalTheory.TripRho.isRhoOfRow_of_frobEig <;> assumption)
