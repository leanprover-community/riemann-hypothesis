module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvCoordsIsBasisAtBaseLatticeOfStdCompanion
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inv_coords_isBasisAt_baseLattice_of_std_companion : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {i : ℕ} (hi : i + 1 ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad) (co : GL (Fin (D.R.N (i + 1))) D.host.E) (a : 𝓞 D.host.E), ¬ (D.what₂.places.resChar w) ∣ T → GlobalTheory.TwU.latCo D.sp (gramN D (i + 1) hi) co a 1 S.Lb = StandardLatticesGL3.stdL D (D.R.N (i + 1)) → IsBaseAt X0 u w hg ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm co⁻¹) (reL (rankN D (i + 1) hi).symm S.Lb) := by
  first | exact @GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo | exact GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo | (intros; apply GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo <;> assumption)
