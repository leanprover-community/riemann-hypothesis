module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePlacesSplitIdempotents
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.type_places_split_idempotents : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ PP ∈ (pk W).Pg, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) = GlobalTheory.FinPl.latV V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) := by
  first | exact @GlobalTheory.LevelPlaces.split_unit | exact GlobalTheory.LevelPlaces.split_unit | (intros; apply GlobalTheory.LevelPlaces.split_unit <;> assumption)
