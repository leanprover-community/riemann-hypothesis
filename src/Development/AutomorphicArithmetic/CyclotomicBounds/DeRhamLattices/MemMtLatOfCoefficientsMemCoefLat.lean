module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelTwistCharacterMemCoefficientIntegersStatement
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LevEnvLevelSubgroupLeLevJAndCharacterEq
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.mem_mtLat_of_coefficients_mem_coefLat :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ F ∈ (baseOf Z c w j).formsC (twVia Z.ρ ι), (∀ a, F ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a) ∈ (baseOf Z c w j).coefLat D.what₂.embLL (labLL D) (intLL D) ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a)) →
      F ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) := by
  intro D X X0 Y S YS Z c w j H ι hι F hF hy
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hc : IsCoefRing D.what₂.embLL (labLL D) (intLL D) :=
    ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => ⟨a, rfl⟩⟩
  refine (Base.mem_mtLat _ _ _ _).2 ⟨hF, fun h => ?_⟩
  obtain ⟨a, γ, k, e⟩ := ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.reps h).exists
  obtain ⟨hk, -⟩ := UpperTheory.KN.levEnv_level_subgroup_le_levJ_and_character_eq D X X0 Y S YS Z c w j H ι hι k
  have h1 := ((Base.mem_formsC _).1 hF).2 γ ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a) ⟨k, hk⟩
  have h2 := Base.act_mem_coefLat hB.frame hc γ _ k (Base.mem_St_of_mem_levJ hk) (hy a)
  have h3 := GlobalTheory.T.level_twist_character_mem_coefficientIntegers D X X0 Y S YS Z c w j H ι hι ⟨k, hk⟩
  have h4 := Submodule.smul_mem _ (⟨_, h3⟩ : intLL D) h2
  subst e
  exact h1 ▸ h4
