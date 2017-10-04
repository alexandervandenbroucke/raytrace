{- | A simple raytracer.

     Author: Alexander Vandenbroucke <alexander.vandenbroucke@gmail.com>
-}

module Main where

import Codec.Picture
import Control.Monad (guard)
import Data.Array.Repa (
  Array,U,
  Z(Z), (:.)((:.)), DIM2,
  fromFunction,
  computeP,
  (!))
import Control.Monad.Identity (Identity,runIdentity)
import Control.Applicative (ZipList(..))


-------------------------------------------------------------------------------
-- Vector3D: 3 dimensional vector and operations

-- | A datatype for double-precision 3 dimensional vectors.
data Vector3D
  = MkV3D
    {-# UNPACK #-} !Double
    {-# UNPACK #-} !Double
    {-# UNPACK #-} !Double
  deriving Show

instance Num Vector3D where
  MkV3D x1 y1 z1 + MkV3D x2 y2 z2 = MkV3D (x1+x2) (y1+y2) (z1+z2)
  {-# INLINE (+) #-}
  MkV3D x1 y1 z1 * MkV3D x2 y2 z2 = MkV3D (x1*x2) (y1*y2) (z1*z2)
  {-# INLINE (*) #-}
  MkV3D x1 y1 z1 - MkV3D x2 y2 z2 = MkV3D (x1-x2) (y1-y2) (z1-z2)
  {-# INLINE (-) #-}
  fromInteger i = MkV3D d d d where d = fromInteger i
  {-# INLINE fromInteger #-}
  abs = undefined
  {-# INLINE abs #-}
  signum (MkV3D x y z) = MkV3D (signum x) (signum y) (signum z)
  {-# INLINE signum #-}

instance Fractional Vector3D where
  MkV3D x1 y1 z1 / MkV3D x2 y2 z2 = MkV3D (x1/x2) (y1/y2) (z1/z2)
  recip (MkV3D x y z) = MkV3D (recip x) (recip y) (recip z)
  fromRational r = MkV3D r' r' r' where r' = fromRational r

-- | Inner product
(*@) :: Vector3D -> Vector3D -> Double
MkV3D x1 y1 z1 *@ MkV3D x2 y2 z2 = x1*x2 + y1*y2 + z1*z2
{-# INLINE (*@) #-}

-- | Outer product
(*#) :: Vector3D -> Vector3D -> Vector3D
MkV3D x1 y1 z1 *# MkV3D x2 y2 z2 =
  MkV3D (y1*z2-z1*y2) (z1*x2-x1*z2) (x1*y2-x2*y1)
{-# INLINE (*#) #-}

-- | 2-norm (aka euclidian norm)
norm :: Vector3D -> Double
norm v = sqrt (v *@ v)
{-# INLINE norm #-}

-- | Normalise a 'Vector3D'.
normalize :: Vector3D -> Vector3D
normalize v@(MkV3D x y z) = MkV3D (x / n) (y/n) (z/n) where
  n = norm v
{-# INLINE normalize #-}

-- | Multiply a 'Vector3D' with a scalar value.
scalar :: Double -> Vector3D -> Vector3D
scalar d (MkV3D x y z) = MkV3D (d*x) (d*y) (d*z)
{-# INLINE scalar #-}

-------------------------------------------------------------------------------
-- Shape: shapes

-- | Ray are formally half-lines with a given start position and direction.
--   This implementation also caches the reciprocal of the Z-component of
--   the direction.
data Ray
  = MkRay
    {
      ray_position  :: !Vector3D,
      ray_direction :: !Vector3D,
      ray_recip     :: !Double
    }
  deriving Show

-- | Smart constructor for 'Ray'.
--   Takes a start position and a (normalised) direction as arguments.
--   This constructor ensures that the absolute values of all components of the
--   direction are at least 2.2*(10**(-308)) and therefore non-zero.
mkray :: Vector3D -> Vector3D -> Ray
mkray position direction@(MkV3D x y z) =
  let x' = clamp x
      y' = clamp y
      z' = clamp z
      clamp d = if abs d <= eps then eps else d
      {-# INLINE clamp #-}
      eps = 2.2*(10**(-308))
  in MkRay position (MkV3D x' y' z') (recip z')

-- | Given a 'Ray' and a point along the ray, return the distance travelled.
--   More  precisely, given ray @r@ and point @p@ return t such that
--
--     @ ray_position r + t * ray_direction r = p @
--
rayDistance :: Ray -> Vector3D -> Double
rayDistance r (MkV3D _ _ pz) =
  let MkV3D _ _ z = ray_position r
  in (pz - z) * ray_recip r
{-# INLINE rayDistance #-}

-- | A 4-tuple of the intersection postion, surface normal at this position,
--   the distance along the ray and the material at that position is returned.
type Intersection = (Vector3D,Vector3D,Double,Material)

-- | Materials specify the diffuse and specular reflexivity as well as the
--   specularity (shinyness) of a 'Shape'.
data Material
  = MkMaterial
    {
      mat_diffuse     :: !PixelRGB8,
      mat_specular    :: !PixelRGB8,
      mat_specularity :: !Double
    }

-- | A 'Shape' is something that can test for intersection with a 'Ray'.
--   When there is an intersection 'Just' an 'Intersection' is returned.
newtype Shape
  = MkShape
    {
      isect :: Ray -> Maybe Intersection
    }

-- | Shapes are monoids.
--   The empty element is a 'Shape' that does not interesect any 'Ray'.
--   The @mappend@ of two 'Shape's is a 'Shape' that returns the interesection
--   that is closest.
instance Monoid Shape where
  mempty  = MkShape (const Nothing)
  r1 `mappend` r2 = MkShape $ \ray -> 
     let isect1 = isect r1 ray
         isect2 = isect r2 ray
     in case (isect1,isect2) of
         (Nothing,_) -> isect2
         (_,Nothing) -> isect1
         (Just (_,_,t1,_), Just (_,_,t2,_)) ->
           if t1 <= t2 then isect1 else isect2
  {-# INLINE mappend #-}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Planes (rectangles)

-- | Create a rectangle.
--   Takes a material, position, width and height and creates the corresponding
--   3D rectangle. Width and height must be orthogonal.
rectangle :: Material -> Vector3D -> Vector3D -> Vector3D -> Shape
rectangle material point width height =
  let normal = normalize (width *# height)
      ww     = width  *@ width
      hh     = height *@ height
      point' = point - scalar 0.5 width - scalar 0.5 height
      d = -(point *@ normal)
  in MkShape $ \ray -> do
      (isect,t) <- planeRayIsect normal d ray
      -- verify within bounds of rectangle
      guard $
        let dV = isect - point'
            dw = dV *@ width
            dh = dV *@ height
        in 0 <= dw && dw <= ww && 0 <= dh && dh <= hh
      return (isect, normal,t,material)

-- | Helper function to decide if a ray intersects a plane.
--   Takes the normal of the plane, it's "d" component and a ray.
--   Returns a tuple of the intersection point and the ray distance to the
--   point in a @Maybe@.
planeRayIsect :: Vector3D -> Double -> Ray -> Maybe (Vector3D,Double)
planeRayIsect normal d ray = do
  isect <- planeLineIsect normal d (ray_position ray) (ray_direction ray)
  -- verify positive ray direction
  let t = rayDistance ray isect
  guard (t >= 0)
  return (isect,t)
{-# INLINE planeRayIsect #-}

-- | Helper function to decide if a line intersects a plane.
--   Takes the normal of the plane, it's "d" component, a point on the line
--   and the direction of the line.
planeLineIsect :: Vector3D -> Double -> Vector3D -> Vector3D -> Maybe Vector3D
planeLineIsect normal d line_position line_dir = 
  let MkV3D a  b  c  = normal
      MkV3D lx ly lz = line_position
      MkV3D a' b' c' = line_dir
      frac = (normal *@ line_dir) / c'
      z = (-d - a*lx - b*ly + (frac-c)*lz)/frac
      x = (a' * (z - lz)/ c') + lx
      y = (b' * (z - lz)/ c') + ly
  in if abs frac <= 0.00001 then -- TODO: Z-face culling!
       Nothing
     else
       Just (MkV3D x y z)
{-# INLINE planeLineIsect #-}
-- ^ this inline gains us about 10 seconds on stacked_cubes :-D
-- Note to self: don't recurse unless necessary.

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Cubes

-- | A cube consisting of a single material
--   Takes a the material, a position vector and the size of a side.
cube :: Material -> Vector3D -> Double -> Shape
cube material point l = colorcube [material] point l

-- | A cube where every side has a different material.
--   The list of materials must be non-empty.
colorcube :: [Material] -> Vector3D -> Double -> Shape
colorcube materials point l = colorcuboid materials point l l l

-- | A cuboid consisting of a single material
--   Takes a the material, a position vector, length, height and depth.
cuboid :: Material -> Vector3D -> Double -> Double -> Double -> Shape
cuboid material point l h d = colorcuboid [material] point l h d

-- | A cube where every side has a different material.
--   The list of materials must be non-empty.
colorcuboid :: [Material] -> Vector3D -> Double -> Double -> Double -> Shape
colorcuboid [] _ _ _ _ = error "colorcuboid: list of materials must not be empty."
colorcuboid materials point l h d =
  let [mtop,mbottom,mfront,mback,mleft,mright] = take 6 $ cycle materials
      l2 = l / 2
      h2 = h / 2
      d2 = d / 2
  in mconcat [
    -- top
    rectangle mtop    (point+MkV3D 0 h2 0) (MkV3D l 0 0) (MkV3D 0 0 (-d)),
    -- bottom
    rectangle mbottom (point-MkV3D 0 h2 0) (MkV3D l 0 0) (MkV3D 0 0 d),
    -- front
    rectangle mfront  (point+MkV3D 0 0 d2) (MkV3D l 0 0) (MkV3D 0 h 0),
    -- back
    rectangle mback   (point-MkV3D 0 0 d2) (MkV3D l 0 0) (MkV3D 0 (-h) 0),
    -- left
    rectangle mleft   (point+MkV3D l2 0 0) (MkV3D 0 h 0) (MkV3D 0 0 d),
    -- right
    rectangle mright  (point-MkV3D l2 0 0) (MkV3D 0 h 0) (MkV3D 0 0 (-d))]

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Color

-- | A class abstracting over color names.
class Color c where
  black,white,red,green,blue,magenta,cyan,yellow,orange,orchid,aquamarine :: c
  

instance Color PixelRGB8 where
  black   = PixelRGB8 0 0 0
  white   = PixelRGB8 255 255 255
  red     = PixelRGB8 255 0   0
  green   = PixelRGB8 0   255 0
  blue    = PixelRGB8 0   0   255
  magenta = PixelRGB8 255 0   255
  cyan    = PixelRGB8 0   255 255
  yellow  = PixelRGB8 255 255 0
  orange  = PixelRGB8 255 134 0
  orchid  = PixelRGB8 153 50  204
  aquamarine = PixelRGB8 69 139 116

instance Color Material where
  black   = MkMaterial black black 1.0
  white   = MkMaterial white white 1.0
  red     = MkMaterial red   red   1.0
  green   = MkMaterial green green 1.0
  blue    = MkMaterial blue  blue  1.0
  magenta = MkMaterial magenta magenta 1.0
  cyan    = MkMaterial cyan    cyan    1.0
  yellow  = MkMaterial yellow  yellow  1.0
  orange  = MkMaterial orange  orange  1.0
  orchid  = MkMaterial orchid  orchid  1.0
  aquamarine = MkMaterial aquamarine aquamarine 1.0
  {-# INLINE black #-}

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Triangle

-- | A triangle.
--   The triangle is identified by 3 points.
--   No corner of the triangle must exceed 90 degrees.
triangle :: Material -> Vector3D -> Vector3D -> Vector3D -> Shape
triangle material pa pb pc =
  let u = pb - pa
      v = pc - pa
      normal = normalize (u *# v)
      d = scalar (-1) pa *@ normal
      cA = pb - pa
      cB = pc - pb
      cC = pa - pc
  in MkShape $ \ray -> do
    (isect,t) <- planeRayIsect normal d ray
    let dA = isect - pa
        dB = isect - pb
        dC = isect - pc
    -- verify within bounds of triangle
    guard ((cA *# dA) *@ normal >= 0)
    guard ((cB *# dB) *@ normal >= 0)
    guard ((cC *# dC) *@ normal >= 0)
    return (isect,normal,t,material)


-------------------------------------------------------------------------------
-- Lights

-- | A light shades a pixel according to the intersection with the shape, as
--   well as the 'Ray' that intersected it.
newtype Light
  = MkLight
    {
      light :: Intersection -> Ray -> PixelRGB8
    }

-- | Lights are monoids.
--   The empty light contributes no shade to a pixel.
--   The 'mappend' of two lights is simply the sum of their contribution,
--   clamped to the maximal color value.
instance Monoid Light where
  mempty = MkLight $ \_ _ -> black
  {-# INLINE mempty #-}
  mappend (MkLight l1) (MkLight l2) = MkLight $ \i ray ->
     let clamp x y = if x + y < x then 255 else x + y
         addPixelRGB8 (PixelRGB8 r1 g1 b1) (PixelRGB8 r2 g2 b2) =
           PixelRGB8 (clamp r1 r2) (clamp g1 g2) (clamp b1 b2)
     in l1 i ray `addPixelRGB8` l2 i ray
  {-# INLINE mappend #-}

-- | Helper function to convert a 'Pixel8' to a Double
p2d :: Pixel8 -> Double
p2d i = fromInteger (toInteger i)
{-# INLINE p2d #-}

-- | Point light source.
--   Takes the world ('Shape'), a diffuse and specular intensity and a
--   position.
pointLight :: Shape -> Double -> Double -> Vector3D -> Light
pointLight world diffuse specular lpos =
  MkLight $ \(ipos,inormal,_,material) ray ->
    let to_light = normalize (lpos - ipos)
        (PixelRGB8 dr dg db) = mat_diffuse material
        (PixelRGB8 sr sg sb) = mat_specular material
        s = mat_specularity material
        ray_to_light = mkray (ipos + scalar 0.00001 to_light) to_light
    in case isect world ray_to_light of
      Just (_,_,t,_) | t <= rayDistance ray_to_light lpos -> black
          -- ^ check if ipos' is between light and ipos ??
      _ ->
        -- note: properly reflection is 2 * (L.N) * N - L but here it's more
        -- convenient to use its inverse.
        let lndot = to_light *@ inormal
            reflection' = to_light - scalar (2 * lndot) inormal
            fDiffuse  = diffuse * max 0 lndot
            fSpecular = 
              if lndot <= 0 then
                0
              else
                specular * (max 0 (reflection' *@ ray_direction ray) ** s)
            f = min 1.0 (fDiffuse + fSpecular)
            r = round $ f * p2d dr
            g = round $ f * p2d dg
            b = round $ f * p2d db
        in PixelRGB8 r g b

-- | Ambient light, simply contributes a given intensity to every pixel.
ambient :: Double -> Light
ambient f = MkLight $ \(_,_,_, MkMaterial (PixelRGB8 ir ig ib) _ _) _ ->
  let r = round $ f * p2d ir
      g = round $ f * p2d ig
      b = round $ f * p2d ib
  in PixelRGB8 r g b

-------------------------------------------------------------------------------
-- Camera: casts (creates) rays.

-- | A camera generates 'Ray's for every pixel.
newtype Camera
  = MkCamera
    {
      cast :: Int -> Int -> Ray
    }

-- | Takes width and height in pixels and returns a 'Camera' that has a fixed
--   fov of 90 degrees, is positioned at the origin and looks along the z-axis.
fixedCamera :: Int -> Int -> Camera
fixedCamera width height =
  let w = fromIntegral width  :: Double -- viewport width in pixels
      h = fromIntegral height :: Double -- viewport height in pixels
      fov = pi/2                  -- horizontal FOV is fixed to 90 degrees
      -- Converting from pixels to world is done by multiplying with a
      -- scaling factor and adding an offset (one for each axis).

      -- SCALING FACTORS
      -- (ratio of world viewport size vs pixel viewport size)
      scaleX = 1.0 / w            -- Here 1.0 is the width of viewport in
                                  -- world units.
      scaleY = scaleX * (-h / w)  -- The viewport height in world units is 
                                  -- determined by the aspect ratio of h and w.
      -- OFFSETS
      -- are difference in world units between viewport midpoint and
      -- picture midpoint. The viewport midpoint is assumed to be the origin.
      -- the picture midpoint is assumed to be the middle of the picture
      -- (width and height / 2).
      dX = negate (scaleX * w/2)
      dY = negate (scaleY * h/2)
      d  = tan(fov/2) * dX  -- distance from the screen
  in MkCamera $ \screenX screenY ->
    let posX = scaleX * (fromIntegral screenX) + dX
        posY = scaleY * (fromIntegral screenY) + dY
        position  = MkV3D posX posY 0 -- camera is always at Z=0
        direction = normalize (MkV3D posX posY d)
    in mkray position direction

-------------------------------------------------------------------------------
-- Ray tracing

-- | Trace the ray generated at a given pixel position.
trace :: Camera -> Light -> Shape -> Int -> Int -> PixelRGB8
trace camera lights world x y = case isect world ray of
  Nothing                 -> black
  Just i -> light lights i ray
  where ray = cast camera x y
{-# INLINE trace #-}

-------------------------------------------------------------------------------
-- Main function

-- The rendering algorithm is O(W * H * L * (N+1)) where L = # (point) lights
--                                                       N = # objects
--                                                       W = width (in pixels)
--                                                       H = height (in pixels)

main :: IO ()
main = 
  let trace' = parallelTrace w h (trace camera lights world)
      -- trace' = trace camera lights world
      -- world  = cylinder blue blue green (MkV3D 0 (-2) (-10)) 20 1 5  `mappend` axes
      -- world  = stacked_cubes
      -- world = triangle_example
      -- (world,lights) = intersection
      -- world = cubes
      camera = fixedCamera w h
      -- light  = pointLight world 0.03 0.2 (MkV3D 2 0 0)
      -- light2 = pointLight world 0.3 1.0 (MkV3D 0 4 (-10))
      -- lights = mconcat [light,light2,ambient 0.2]
      -- (world,lights) = spec_test
      world = mconcat [
        tree (MkV3D (-2) (-1) (-4)),
        tree  (MkV3D (-1) (-1) (-6)),
        tree  (MkV3D 1 (-1) (-2)),
        rectangle white (MkV3D 0 (-1) (-4)) (MkV3D 0 0 10) (MkV3D 10 0 0)]
      lights = mconcat [pointLight world 0.8 0.8 (MkV3D 0 100 0), ambient 0.5]
      -- (world,lights) = intersection
      -- (world,lights) = bsp
      w      = 1024
      h      = 1024
  in saveBmpImage "trace.bmp" $ ImageRGB8 $ generateImage trace' w h

parallelTrace :: Int -> Int
              -> (Int -> Int -> PixelRGB8)
              -> Int -> Int
              -> PixelRGB8
parallelTrace w h trace x y =
  let tracedD = fromFunction (Z :. h :. w) trace' where
        trace' (Z :. y :. x) = (r,g,b) where PixelRGB8 r g b = trace x y
      traced :: Array U DIM2 (Pixel8,Pixel8,Pixel8)
      traced = runIdentity $ computeP tracedD
      (r,g,b) = traced ! (Z :. y :. x)
  in PixelRGB8 r g b
{-# INLINE parallelTrace #-}

planes = mconcat [
  rectangle red   (MkV3D (-0.5) (-0.5) (-2))   (MkV3D 1 0 0) (MkV3D 0 1 0),
  rectangle blue  (MkV3D (-1)   (-0.5) (-1.5)) (MkV3D 0 1 0) (MkV3D 0 0 1),
  rectangle green (MkV3D (-0.5) (-1)   (-1.5)) (MkV3D 1 0 0) (MkV3D 0 0 (-1))]

axes = mconcat [
  rectangle red   centre (MkV3D 1 0 0) (MkV3D 0 0.1 0),
  rectangle blue  centre (MkV3D 0 1 0) (MkV3D 0 0 0.1),
  rectangle green centre (MkV3D 0.1 0 0) (MkV3D 0 0 (-1)),
  triangle red   (centre + MkV3D 0.6   0     0)
                 (centre + MkV3D 0.5   0.05  0)
                 (centre + MkV3D 0.5 (-0.05) 0),
  triangle blue  (centre + MkV3D 0 0.6   0)
                 (centre + MkV3D 0 0.5   0.05)
                 (centre + MkV3D 0 0.5 (-0.05)),
  triangle green (centre + MkV3D   0     0 0.6)
                 (centre + MkV3D   0.05  0 0.5)
                 (centre + MkV3D (-0.05) 0 0.5)
  ]
  where centre = MkV3D (-0.5) (-0.5) (-1)


cubes =
  mconcat [ 
    colorcube colors (MkV3D (-2) 0 (-6)) 1,
    colorcube colors (MkV3D 0 (-2) (-6)) 1,
    colorcube colors (MkV3D 2 0    (-6)) 1,
    colorcube colors (MkV3D 0 2    (-6)) 1,
    colorcube colors (MkV3D 0 0    (-6)) 1]
  where colors = [red,green,blue,magenta,cyan,aquamarine,yellow,orange,orchid]

stacked_cubes =
  mconcat [
    -- floor
    rectangle blue (MkV3D 0 (-2) 0) (MkV3D 20 0 0) (MkV3D 0 0 (-40)),
    -- ceiling
    rectangle blue (MkV3D 0 (4.5) 0) (MkV3D 20 0 0) (MkV3D 0 0 (40)),
    -- cube
    colorcube colors (MkV3D (-2) (-1.5) (-6)) 1,
    -- light housing
    cube white (MkV3D 0 4.2 (-10)) 0.1,
    cube white (MkV3D 0 3.8 (-10)) 0.1,
    rectangle green (MkV3D (-0.2) 4 (-10))   (MkV3D 0 (-0.5) 0) (MkV3D 0 0 (-0.3)),
    rectangle green (MkV3D (0.2)  4 (-10))   (MkV3D 0 (-0.5) 0) (MkV3D 0 0 0.3),
    rectangle green (MkV3D 0      4 (-9.8))  (MkV3D 0 0.5    0) (MkV3D 0.3 0 0),
    rectangle green (MkV3D 0      4 (-10.2)) (MkV3D 0 (-0.5) 0) (MkV3D 0.3 0 0),
    -- wall
    rectangle orange (MkV3D 2.2 (-0.5) (-10)) (MkV3D 0 12 0) (MkV3D (-5) 0 (-10))]
  where colors = [red,green,yellow]

triangle_example =
  mconcat [
    -- background piece
    rectangle cyan (MkV3D 0    0 (-10)) (MkV3D 4.0   0    0)    (MkV3D 0 4.0 0),
    rectangle cyan (MkV3D (-3) 0 (-9))  (MkV3D (2.0) 0  (-2.0)) (MkV3D 0 4.0 0),
    rectangle cyan (MkV3D   3  0 (-9))  (MkV3D (2.0) 0  (2.0))  (MkV3D 0 4.0 0),
    -- yellow cube
    cube yellow (MkV3D 0 (-1.5) (-5)) 1.0,
    -- triangle
    triangle orange (MkV3D 0 1 (-4)) (MkV3D (-1) 0  (-4)) (MkV3D 1 0  (-4)),
    -- other things
    rectangle green (MkV3D 0 0 (-3)) (MkV3D 1 0 0)  (MkV3D 0 1 0),
    rectangle blue  (MkV3D 0 (-2) 0) (MkV3D 20 0 0) (MkV3D 0 0 (-40))]

cylinder :: Material -> Material -> Material
         -> Vector3D -> Int -> Double -> Double -> Shape
cylinder topM botM mantleM point n h r  =
  let points =
        [ (r*cos (i*alpha),r*sin (i*alpha)) | i <- [0..(n'-1)]] ++ [(r,0)]
      topPoints    = ZipList [point + MkV3D x   h2  z | (x,z) <- points]
      botPoints    = ZipList [point + MkV3D x (-h2) z | (x,z) <- points]
      mantlePoints = ZipList [point + MkV3D x   0   z | (x,z) <- points]
      normals      = ZipList [MkV3D (x/r) 0 (z/r)     | (x,z) <- points]
      topPoint = point + MkV3D 0   h2  0
      botPoint = point - MkV3D 0 (-h2) 0
      alpha    = 2*pi/n'
      h2       = h / 2
      n'       = fromInteger (toInteger n)
      tailZL    = ZipList . tail . getZipList
      mconcatZL = mconcat . getZipList
      --
      top =
        mconcatZL
        $ triangle topM topPoint
        <$> tailZL topPoints
        <*> topPoints
      bot =
        mconcatZL
        $ triangle botM  botPoint
        <$> botPoints
        <*> tailZL botPoints
      mantle =
        mconcatZL
        $ mantleRect
        <$> mantlePoints
        <*> tailZL mantlePoints
        <*> normals
        <*> tailZL normals
      -- a special rectangle that has interpolated normals
      mantleRect p1 p2 n1 n2 =
        let p  = scalar (0.5) (p1 + p2)
            dP = p1 - p2 -- aka the width of this piece
            dN = n1 - n2
            dNdP  = dN / dP
        in MkShape $ \ray -> do
          (i,_,t,color) <- isect (rectangle mantleM p dP (MkV3D 0 h 0)) ray
          let MkV3D nx _ nz = n2 + (i - p2) * dNdP
              -- linearly interpolated normal
          return (i, MkV3D nx 0 nz,t,color)
  in bot `mappend` top `mappend` mantle

spec_test :: (Shape,Light)
spec_test =
  let world = mconcat [
        rectangle blue       (MkV3D 0   (-2) 0)  (MkV3D 20 0 0)     (MkV3D 0 0 (-40)),
        rectangle blue       (MkV3D 0    10  0)  (MkV3D 20 0 0)     (MkV3D 0 0 (-40)),
        rectangle white      (MkV3D (-2) 0 (-4)) (MkV3D 0 6 0)      (MkV3D 0 0 6),
        rectangle spec_white (MkV3D 2    0 (-4)) (MkV3D (-0.5) 0 6) (MkV3D 0 6 0)]
      light =
        pointLight world 0.3 0.6 (MkV3D 0 0 (-4))
        `mappend`
        pointLight world 0.0 1.0 (MkV3D (-3) 0 (-10))
      spec_white = white{mat_specularity=400} 
   in (world, light)

intersection :: (Shape,Light)
intersection =
  let world = mconcat [
        cylinder red red red (MkV3D 0 (-1) (-3)) 20 2 0.02,
        rectangle orange (MkV3D 0 (-1) (-3)) (MkV3D 1 0 1) (MkV3D 2 0 (-2))]
      --
      light = ambient 0.5 `mappend` pointLight world 0.5 0.2 (MkV3D 1 1 (-3))
  in (world,light)

tree :: Vector3D -> Shape
tree point =
  let p0 = point + MkV3D 0 0.35 0
      pyramid c p b h =
        let b2 = b / 2
            top        = p + MkV3D 0     h 0
            frontLeft  = p + MkV3D (-b2) 0 b2
            frontRight = p + MkV3D b2    0 b2
            backRight  = p + MkV3D b2    0 (-b2)
            backLeft   = p + MkV3D (-b2) 0 (-b2)
        in mconcat [
          --front
          triangle c top frontLeft frontRight,
          -- left
          triangle c top backLeft frontLeft,
          -- right
          triangle c top frontRight backRight,
          -- back
          triangle c top backRight backLeft]
      darkgreen =
        MkMaterial
        { 
          mat_diffuse  = PixelRGB8 0 50 0,
          mat_specular = PixelRGB8 0 0 0,
          mat_specularity = 1.0
        }
      darkbrown =
        MkMaterial
        { 
          mat_diffuse  = PixelRGB8 50 50 0,
          mat_specular = PixelRGB8 50 50 0,
          mat_specularity = 1.0
        }
      specwhite = white{mat_diffuse = PixelRGB8 100 100 100,mat_specularity=100}
  in mconcat [
    mconcat [ pyramid darkgreen (p0 + MkV3D 0 (0.1*y) 0) (1.0 - 0.1*y) 1
            | y <- [0..4.0] ],
    pyramid specwhite (p0 + MkV3D 0 0.5 0) 0.5 1,
    -- cuboid darkbrown (p0-MkV3D 0 0.35 0) 0.5 0.7 0.5]
    cylinder black black darkbrown (p0-MkV3D 0 0.35 0) 12 0.7 0.25]
