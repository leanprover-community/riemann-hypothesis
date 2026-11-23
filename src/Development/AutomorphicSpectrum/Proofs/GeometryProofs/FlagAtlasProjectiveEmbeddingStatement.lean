module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFrameChangeTriangular
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagAtlasProjectiveEmbedding
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

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.flag_atlas_projective_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, Z ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ Z)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∃ d : ℕ, SmoothOfRelativeDimension d (π ≫ Y.s) ∧ IsProjOver (π ≫ Y.s) := by
  first | exact @GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj | exact GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj | (intros; apply GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj <;> assumption)
