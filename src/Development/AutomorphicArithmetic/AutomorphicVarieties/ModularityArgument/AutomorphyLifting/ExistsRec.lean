module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem exRec (N : GlobalTheory.Mem.LiteralAutomorphy.LitN) (h : IsPlaceOver A w) : ∃ rc, IsRec h rc :=
  ((GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein N.loc.llc N.loc.conv N.loc.dzc N.loc.dzi N.loc.brauer N.loc.chev
    N.aut.art N.loc.exh N.loc.multi N.loc.cos N.loc.zel N.loc.geo N.loc.bz).1 E Ω A w h).exists

theorem exRec' (_N : GlobalTheory.Mem.LiteralAutomorphy.LitN) (h : IsPlaceOver A w) : ∃ rc, IsRecT h rc := recTExists E Ω A w h

end UpperTheory.V.Z.Win
