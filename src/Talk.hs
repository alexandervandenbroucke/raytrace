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
import Data.Monoid ((<>))



-- 1) Rays

-- type Vector3D = ()

data Ray
  = MkRay
    {
      ray_position  :: Vector3D,
      ray_direction :: Vector3D
    } deriving Show

-- smart constructor: make sure all components are non-zero
mkray :: Vector3D -> Vector3D -> Ray
mkray p (MkV3D dx dy dz) =
  MkRay
  {
    ray_position  = p
    ray_direction = MkV3D (clamp dx) (clamp dy) (clamp dz)
  }
  where clamp d = if abs d <= eps then eps else d
        {-# INLINE clamp #-}
        eps = 2.2*(10**(-308))

-- 2) Vectors

data Vector3D = MkV3D !Double ! Double !Double deriving Show

instance Num Vector3D where
  MkV3D x1 y1 z1 + MkV3D x2 y2 z2 = MkV3D (x1+x2) (y1+y2) (z1+z2)
  MkV3D x1 y1 z1 * MkV3D x2 y2 z2 = MkV3D (x1*x2) (y1*y2) (z1*z2)
  MkV3D x1 y1 z1 - MkV3D x2 y2 z2 = MkV3D (x1-x2) (y1-y2) (z1-z2)
  abs (MkV3D x y z) = MkV3D (abs x) (abs y) (abs z)
  signum (MkV3D x y z) = MkV3D (signum x) (signum y) (signum z)
  fromInteger i = MkV3D i' i' i' where i' = fromInteger i

(*@) :: Vector3D -> Vector3D -> Double
MkV3D x1 y1 z1 *@ MkV3D x2 y2 z2 = x1*x2 + y1*y2 + z1*z2

(*#) :: Vector3D -> Vector3D -> Vector3D
MkV3D x1 y1 z1 *# MkV3D x2 y2 z2 =
  MkV3D (y1*z2-z1*y2) (z1*x2-x1*z2) (x1*y2-x2*y1)
{-# INLINE (*#) #-}

scalar :: Double -> Vector3D -> Vector3D
scalar t (MkV3D x y z) = MkV3D (t*x) (t*y) (t*z)
{-# INLINE scalar #-}

norm :: Vector3D -> Double
norm v = sqrt (v *@ v)

normalize :: Vector3D -> Vector3D
normalize v = scalar (recip (norm v)) v

-- 3) Shapes

-- 3.1) Intersections

type Color = PixelRGB8

white, black, red, green, blue :: Color
white = PixelRGB8 255 255 255
black = PixelRGB8 0 0 0
red   = PixelRGB8 255 0 0
green = PixelRGB8 0 255 0
blue  = PixelRGB8 0 0 255

type Intersection = (Color,Vector3D,Vector3D)

-- 3.2 Shape

newtype Shape
  = MkShape
    {
      isect :: Ray -> Maybe Intersection
    }

-- 3.3 Rectangle (switch back to slides)

-- 3.3.1 intersecting planes and lines

-- | Helper for 'planeLineIsect'
planeLineIsect :: Vector3D -> Double -> Vector3D -> Vector3D -> Maybe Vector3D
planeLineIsect normal d line_position line_dir = 
  let MkV3D a  b  c  = normal
      MkV3D lx ly lz = line_position
      MkV3D a' b' c' = line_dir
      frac = (normal *@ line_dir) / c'
      z = (-d - a*lx - b*ly + (frac-c)*lz)/frac
      x = (a' * (z - lz)/ c') + lx
      y = (b' * (z - lz)/ c') + ly
  in if abs frac <= 0.00001 then
       Nothing
     else
       Just (MkV3D x y z)
{-# INLINE planeLineIsect #-}

rectangle :: Color -> Vector3D -> Vector3D -> Vector3D -> Shape
rectangle c point width height =
  let normal = normalize (width  *# height)
      d      = -(point  *@ normal)
      ww     =   width  *@ width
      hh     =   height *@ height
      point' =   point - scalar 0.5 width - scalar 0.5 height
  in MkShape $ \ray -> do
    i <- planeLineIsect normal d (ray_position ray) (ray_direction ray)
    guard $
      (ray_direction ray) *@ (i - ray_position ray) >= 0
    guard $
      let dV = i - point'
          dw = dV *@ width
          dh = dV *@ height
      in 0 <= dw && dw <= ww && 0 <= dh && dh <= hh
    return (c,i,normal)

-- 4. Generating rays: cameras

newtype Camera
  = MkCamera
    {
      cast :: Int -> Int -> Ray
    } 

fixedCamera :: Int -> Int -> Camera
fixedCamera width height = 
  let w = fromIntegral width
      h = fromIntegral height
      fov = pi/2
      scaleX = 1.0 / w
      scaleY = scaleX * (-h / w)
      dX = 0 - scaleX * w/2
      dY = 0 - scaleY * h/2
      d = tan(fov/2)  * dX
  in MkCamera $ \screenX screenY ->
    let posX = scaleX * (fromIntegral screenX) + dX
        posY = scaleY * (fromIntegral screenY) + dY
        position  = MkV3D posX posY 0
        direction = normalize (MkV3D posX posY d)
    in mkray position direction

-- 5. tracing rays
trace :: Shape -> Camera -> Int -> Int -> PixelRGB8
trace world camera x y = case isect world (cast camera x y) of
  Nothing      -> black
  Just (c,_,_) -> c

main1 :: IO ()
main1 =
  let world  = cube [red,green,blue,white,black] 2.0 (MkV3D 0 (-2) (-4))
      width  = 512
      height = 512
      camera = fixedCamera width height
  in saveBmpImage "trace.bmp"
     $ ImageRGB8
     $ generateImage (parallel width height $ trace world camera) width height

parallel :: Int -> Int
              -> (Int -> Int -> PixelRGB8)
              -> Int -> Int
              -> PixelRGB8
parallel w h trace x y =
  let tracedD = fromFunction (Z :. h :. w) trace' where
        trace' (Z :. y :. x) = (r,g,b) where PixelRGB8 r g b = trace x y
      traced :: Array U DIM2 (Pixel8,Pixel8,Pixel8)
      traced = runIdentity $ computeP tracedD
      (r,g,b) = traced ! (Z :. y :. x)
  in PixelRGB8 r g b
{-# INLINE parallel #-}

-- 6. combining shapes
instance Monoid Shape where
  mempty = MkShape (const Nothing)
  mappend s1 s2 = MkShape $ \ray -> case (isect s1 ray,isect s2 ray) of
    (Nothing, i) -> i
    (i, Nothing) -> i
    (Just i1@(_,p1,_), Just i2@(_,p2,_)) ->
      Just $
        let d1 = v *@ v where v = p1 - ray_position ray
            d2 = v *@ v where v = p2 - ray_position ray
        in if d1 <= d2 then i1 else i2


cube :: [Color] -> Double -> Vector3D -> Shape
cube colours s p =
  let s2 = s / 2
      [ctop,cbottom,cfront,cback,cleft,cright] = take 6 $ cycle colours
  in
    -- top
    rectangle ctop (p+MkV3D 0 s2 0) (MkV3D s 0 0) (MkV3D 0 0 (-s))
    <>
    --bottom
    rectangle cbottom (p-MkV3D 0 s2 0) (MkV3D 0 0 s) (MkV3D s 0 0) 
    <>
    -- front
    rectangle cfront  (p+MkV3D 0 0 s2) (MkV3D s 0 0) (MkV3D 0 s 0)
    <>
    -- back
    rectangle cback   (p-MkV3D 0 0 s2) (MkV3D s 0 0) (MkV3D 0 (-s) 0)
    <>
    -- left
    rectangle cleft   (p+MkV3D s2 0 0) (MkV3D 0 s 0) (MkV3D 0 0 s)
    <>
    -- right
    rectangle cright  (p-MkV3D s2 0 0) (MkV3D 0 s 0) (MkV3D 0 0 (-s))

-- 7. Let there be light (and shadows)
newtype Light = MkLight { shade :: Intersection -> Color }

instance Monoid Light where
  mempty = MkLight (const black)
  mappend l1 l2 = MkLight $ \i -> addColor (shade l1 i) (shade l2 i) where
    addColor (PixelRGB8 r1 g1 b1) (PixelRGB8 r2 g2 b2) =
      PixelRGB8 (clamp r1 r2) (clamp g1 g2) (clamp b1 b2)
    clamp w1 w2 = if w1 + w2 < w1 || w1 + w2 < w2 then 255 else w1 + w2

ambient :: Double -> Light
ambient intensity = MkLight $ \(PixelRGB8 r g b,_,_) ->
  let r' = round $ intensity * p2d r
      g' = round $ intensity * p2d g
      b' = round $ intensity * p2d b
  in PixelRGB8 r' g' b'

pointLight :: Double -> Vector3D -> Shape -> Light
pointLight intensity lp world = MkLight $ \(PixelRGB8 r g b,p,n) ->
  let to_light = normalize (lp - p)
  in case isect world (mkray (p + scalar 0.00001 to_light) to_light) of
    Just (_,p',_)
      | (lp - p') *@ to_light >= 0 -> black
    _ ->
      let f = min 1 (max 0 (to_light *@ n) * intensity)
          r' = round $ f * p2d r
          g' = round $ f * p2d g
          b' = round $ f * p2d b
      in PixelRGB8 r' g' b'

-- | Helper function to convert a 'Pixel8' to a Double
p2d :: Pixel8 -> Double
p2d i = fromInteger (toInteger i)
{-# INLINE p2d #-}

traceAndShade :: Shape -> Camera -> Light -> Int -> Int -> PixelRGB8
traceAndShade world camera lights x y = case isect world (cast camera x y) of
  Nothing -> black
  Just i  -> shade lights i


main2 :: IO ()
main2 =
  let world  = cube [red,green,blue,white,black] 2.0 (MkV3D 1 (-2) (-6))
               <>
               rectangle blue (MkV3D 0 (-5) 0) (MkV3D 20 0 0) (MkV3D 0 0 (-50))
      width  = 512
      height = 512
      camera = fixedCamera width height
      lights = ambient 0.1
               <>
               pointLight 0.3 (MkV3D 0 0 0) world
               <>
               pointLight 0.6 (MkV3D (-1) 3 (-3)) world
      tr = parallel width height $ traceAndShade world camera lights
  in saveBmpImage "trace.bmp"
     $ ImageRGB8
     $ generateImage tr width height


----------- MAIN FUNCTION
main :: IO ()
main = main2
