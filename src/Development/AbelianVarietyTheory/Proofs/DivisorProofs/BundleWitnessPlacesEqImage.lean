module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Div.PgTie


open Classical in
theorem image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {Pr : Formalism.L2.Col.Primes X} {Pr' : Formalism.L2.Col.Primes X'} (hP : HEq Pr Pr') :
    Pr.vGs.image (Formalism.L2.Host.CT.plMap s.iE) = Pr'.vGs.image (Formalism.L2.Host.CT.plMap s'.iE) := by
  subst hX
  cases hs
  cases hP
  rfl

theorem plMap_refl {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.Host.CT.plMap (RingEquiv.refl E) P = P := by
  ext x
  exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x


open Classical in
theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  rw [show Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id from funext plMap_refl, Finset.image_id]


end GlobalTheory.Div.PgTie
