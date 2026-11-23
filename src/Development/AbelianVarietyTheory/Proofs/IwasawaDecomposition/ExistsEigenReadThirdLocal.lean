module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PointGlobalSectionsNeBot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.HeightCounting.Up.ThirdIdx

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem nonempty_divX (Z : RationalReadingWithoutCongruence R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) : Nonempty (DivX D) := by
  obtain ⟨G, V, -⟩ := GlobalTheory.PointGeometry.exists_geo D.what₂.LL
  exact ⟨GlobalTheory.provisionalDivX D G V (fun p _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some)
    (fun p _ r => (GlobalTheory.nonempty_admissibleModel _ p _ (max r 2) 1 (by omega)).some) fun k =>
    ⟨mjH_noEta Z k, jM_noEta Z k, mjH_good_noEta Z hH k, jM_basis_noEta Z hH k, jM_lat_noEta Z hP hH k,
      mjLat_sub_noEta Z hP hH k, MjModel.jM_metric_all_noEta Z hH k⟩⟩

theorem nonempty_ix (hH : Holds R F) : Nonempty A3.A.fam.base.Ix := by
  obtain ⟨p⟩ := GlobalTheory.Div.nonempty_ix_of_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hH.ok hH.prim.block (hH.prim.pos false)
  exact ⟨p.1.1, Formalism.L2.DIV.InertDat3.mem_ixFin_fst _ (hH.ok.ok2.what₂ A3.A.μ0).comm p.2⟩

end GlobalTheory.HeightCounting.Up.ThirdIdx

namespace GlobalTheory.HeightCounting.Up.ThirdIdx

end GlobalTheory.HeightCounting.Up.ThirdIdx

end
