module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.HL.placesLat_gcoordLat_eq : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (𝓞 D.host.E) (VS D).V), GlobalTheory.LocOver.Ext p σ g → (placesOf Z).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ)) := by
  intro D Z T T' F0 F0' FP G c σ p g Λ hE
  unfold GlobalTheory.HL.GCoord.lat GlobalTheory.HL.Places.lat GlobalTheory.HL.WCoord.lat Formalism.MainNotions.S.LocNG.img Formalism.L2.SG.TermLoc.lattice₂
  rw [Submodule.map_span, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g (baseChange₂ D p x), ⟨baseChange₂ D p x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    show (c.c p).e (g (baseChange₂ D p x)) = (placesOf Z).bc p (c.e (σ x))
    rw [hE x, c.compat p (σ x)]
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨c.e (σ x), ⟨x, hx, rfl⟩, ?_⟩
    show (placesOf Z).bc p (c.e (σ x)) = (c.c p).e (g (baseChange₂ D p x))
    rw [hE x, c.compat p (σ x)]
