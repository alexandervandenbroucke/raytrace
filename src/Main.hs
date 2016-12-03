{-# LANGUAGE BangPatterns #-}

module Main where

import Codec.Picture
import Control.Monad (guard)
import Data.Array.Repa as Repa hiding (Shape,map)
import Control.Monad.Identity (Identity,runIdentity)


-------------------------------------------------------------------------------
-- Vector3D: 3 dimensional vector and operations

data Vector3D = MkV3D !Double !Double !Double deriving Show

instance Num Vector3D where
  MkV3D x1 y1 z1 + MkV3D x2 y2 z2 = MkV3D (x1+x2) (y1+y2) (z1+z2)
  MkV3D x1 y1 z1 * MkV3D x2 y2 z2 = MkV3D (x1*x2) (y1*y2) (z1*z2)
  MkV3D x1 y1 z1 - MkV3D x2 y2 z2 = MkV3D (x1-x2) (y1-y2) (z1-z2)
  fromInteger i = MkV3D d d d where d = fromInteger i
  abs = undefined
  signum (MkV3D x y z) = MkV3D (signum x) (signum y) (signum z)

-- inner product
(*@) :: Vector3D -> Vector3D -> Double
MkV3D x1 y1 z1 *@ MkV3D x2 y2 z2 = x1*x2 + y1*y2 + z1*z2
{-# INLINE (*@) #-}

-- outer product
(*#) :: Vector3D -> Vector3D -> Vector3D
MkV3D x1 y1 z1 *# MkV3D x2 y2 z2 =
  MkV3D (y1*z2-z1*y2) (z1*x2-x1*z2) (x1*y2-x2*y1)
{-# INLINE (*#) #-}

norm :: Vector3D -> Double
norm v = sqrt (v *@ v)
{-# INLINE norm #-}

normalize :: Vector3D -> Vector3D
normalize v@(MkV3D x y z) = MkV3D (x / n) (y/n) (z/n) where
  n = norm v
{-# INLINE normalize #-}

scalar :: Double -> Vector3D -> Vector3D
scalar d (MkV3D x y z) = MkV3D (d*x) (d*y) (d*z)
{-# INLINE scalar #-}

-------------------------------------------------------------------------------
-- Shape: shapes
data Ray
  = MkRay
    {
      ray_position  :: Vector3D,
      ray_direction :: Vector3D
    }
  deriving Show

newtype Shape
  = MkShape
    {
      isect :: Ray -> Maybe (Vector3D,Vector3D,PixelRGB8)
    }

instance Monoid Shape where
  mempty  = MkShape $ \_ -> Nothing
  r1 `mappend` r2 = MkShape $ \ray -> 
     let isect1 = isect r1 ray
         isect2 = isect r2 ray
     in case (isect1,isect2) of
         (Nothing,_) -> isect2
         (_,Nothing) -> isect1
         (Just (i1,_,_), Just (i2,_,_)) ->
           let d1 = let d = ray_position ray - i1 in d *@ d
               d2 = let d = ray_position ray - i2 in d *@ d
           in if d1 <= d2 then isect1 else isect2

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Planes, more like parallelograms

rectangle :: PixelRGB8 -> Vector3D -> Vector3D -> Vector3D -> Shape
rectangle color point width height =
  let normal = normalize (width *# height)
      ww     = width  *@ width
      hh     = height *@ height
      point' = point - scalar 0.5 width - scalar 0.5 height
      d = scalar (-1) point *@ normal
  in MkShape $ \ray -> do
      isect <- planeLineIsect normal d (ray_position ray) (ray_direction ray)
      -- verify positive ray direction
      guard $
        (ray_direction ray) *@ (isect - ray_position ray) >= 0
      -- verify within bounds of square
      guard $
        let dV = isect - point'
            dw = dV *@ width
            dh = dV *@ height
        in 0 <= dw && dw <= ww && 0 <= dh && dh <= hh
      return (isect, normal, color)

planeLineIsect :: Vector3D -> Double -> Vector3D -> Vector3D -> Maybe Vector3D
planeLineIsect normal d line_position line_dir =
  let MkV3D a  b  c  = normal
      MkV3D lx ly lz = line_position
      MkV3D a' b' c' = line_dir
  in if c == 0 || c' == 0 then
       if a == 0 || a' == 0 then
         if b == 0 || b' == 0 then
           Nothing
         else do
           MkV3D ix iz iy <-
             planeLineIsect' (MkV3D a c b) d (MkV3D lx lz ly) (MkV3D a' c' b')
           Just (MkV3D ix iy iz)
       else do
         MkV3D iz iy ix <-
           planeLineIsect' (MkV3D c b a) d (MkV3D lz ly lx) (MkV3D c' b' a')
         Just (MkV3D ix iy iz)
     else
       planeLineIsect' normal d line_position line_dir

planeLineIsect' :: Vector3D -> Double -> Vector3D -> Vector3D -> Maybe Vector3D
planeLineIsect' normal d line_position line_dir = 
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
{-# INLINE planeLineIsect' #-}
-- ^ this inline gains us about 10 seconds on stacked_cubes :-D
-- Note to self: don't recurse unless necessary.

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Cubes

cube :: PixelRGB8 -> Vector3D -> Double -> Shape
cube color point l = colorcube [color] point l

colorcube :: [PixelRGB8] -> Vector3D -> Double -> Shape
colorcube [] _ _ = error "colorcube: list of colors must not be empty."
colorcube colors point l =
  let [ctop,cbottom,cfront,cback,cleft,cright] = take 6 $ cycle colors
      l2 = l / 2
  in mconcat [
    -- top
    rectangle ctop    (point+MkV3D 0 l2 0) (MkV3D l 0 0) (MkV3D 0 0 (-l)),
    -- bottom
    rectangle cbottom (point-MkV3D 0 l2 0) (MkV3D l 0 0) (MkV3D 0 0 l),
    -- front
    rectangle cfront  (point+MkV3D 0 0 l2) (MkV3D l 0 0) (MkV3D 0 l 0),
    -- back
    rectangle cback   (point-MkV3D 0 0 l2) (MkV3D l 0 0) (MkV3D 0 (-l) 0),
    -- left
    rectangle cleft   (point+MkV3D l2 0 0) (MkV3D 0 l 0) (MkV3D 0 0 l),
    -- right
    rectangle cright  (point-MkV3D l2 0 0) (MkV3D 0 l 0) (MkV3D 0 0 (-l))]

black, white :: PixelRGB8
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
{-# INLINE black #-}


-------------------------------------------------------------------------------
-- Lights

data Light
  = MkLight
    {
      light :: Vector3D -> Vector3D -> PixelRGB8 -> PixelRGB8
    }

instance Monoid Light where
  mempty = MkLight $ \_ _ _ -> black
  {-# INLINE mempty #-}
  mappend (MkLight l1) (MkLight l2) = MkLight $ \ipos inormal intensity ->
     let clamp x y = if x + y < x then 255 else x + y
         addPixelRGB8 (PixelRGB8 r1 g1 b1) (PixelRGB8 r2 g2 b2) =
           PixelRGB8 (clamp r1 r2) (clamp g1 g2) (clamp b1 b2)
     in l1 ipos inormal intensity `addPixelRGB8` l2 ipos inormal intensity
  {-# INLINE mappend #-}

p2d :: Pixel8 -> Double
p2d i = fromInteger (toInteger i)
{-# INLINE p2d #-}

-- | Point specular light source
pointLight :: Shape -> Double -> Vector3D -> Light
pointLight world intensity position =
  MkLight $ \ipos inormal (PixelRGB8 ir ig ib) ->
    let to_light = normalize (position - ipos)
    in case isect world (MkRay (ipos + scalar 0.00001 to_light) to_light) of
      Just (ipos',_,_)
        | (position - ipos') *@ to_light >= 0 -> black
      _ ->
        let f = max 0 (to_light *@ inormal)
            r = round $ f * p2d ir * intensity
            g = round $ f * p2d ig * intensity
            b = round $ f * p2d ib * intensity
        in PixelRGB8 r g b

-- | Ambient lighting
ambient :: Double -> Light
ambient f = MkLight $ \_ _ (PixelRGB8 ir ig ib) ->
  let r = round $ f * p2d ir
      g = round $ f * p2d ig
      b = round $ f * p2d ib
  in PixelRGB8 r g b

-------------------------------------------------------------------------------
-- Camera: casts (creates) rays.

data Camera
  = MkCamera
    {
      cast :: Int -> Int -> Ray
    }

fixedCamera :: Int -> Int -> Camera
fixedCamera width height =
  let w = fromIntegral width  :: Double
      h = fromIntegral height :: Double
      fov = pi/2
      scaleX = 1.0 / w
      scaleY = scaleX * (-h) / w
      dX = (-0.5 + 0.5) / 2 - scaleX * (w - 0)/2
      dY = (-0.5 + 0.5) / 2 - scaleY * (h - 0)/2
      d  = tan(fov/2) * dX -- fov : 90 degrees (pi/2 / 2)
  in MkCamera $ \screenX screenY ->
    let posX = scaleX * (fromIntegral screenX) + dX
        posY = scaleY * (fromIntegral screenY) + dY
        position  = MkV3D posX posY 0 -- camera is always at Z=0
        direction = normalize (MkV3D posX posY d)
    in MkRay position direction

-------------------------------------------------------------------------------
-- Ray tracing

trace :: Camera -> Light -> Shape -> Int -> Int -> PixelRGB8
trace camera lights world x y = case isect world (cast camera x y) of
  Nothing               -> black
  Just (ipos,inormal,c) -> light lights ipos inormal c
{-# INLINE trace #-}
-------------------------------------------------------------------------------
-- Main function

-- The rendering algorithm is O(W * H * L * (N+1)) where L = # (point) lights
--                                                       N = # objects
--                                                       W = width (in pixels)
--                                                       H = height (in pixels)

main :: IO ()
main = 
  let trace' =
        parallelTrace w h (trace camera lights world)
        -- trace camera lights world
      world  = stacked_cubes
      camera = fixedCamera w h
      light  = pointLight world 0.7 (MkV3D 2 0 0)
      light2 = pointLight world 0.7 (MkV3D 0 4 (-10))
      lights = mconcat [light, light2, ambient 0.1]
      colors = [red,green,blue,magenta,cyan,yellow,orange,orchid,aquamarine]
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
  rectangle blue  (MkV3D (-1)   (-0.5) (-1.5)) (MkV3D 0 1 0) (MkV3D 0 0 (1)),
  rectangle green (MkV3D (-0.5) (-1)   (-1.5)) (MkV3D 1 0 0) (MkV3D 0 0 (-1))]

cubes =
  let colors = [red,green,blue,magenta,cyan,aquamarine,yellow,orange,orchid]
  in colorcube colors (MkV3D (-2) 0 (-6)) 1
     `mappend`
     colorcube colors (MkV3D 0 (-2) (-6)) 1
     `mappend`
     colorcube colors (MkV3D 2 0 (-6)) 1
     `mappend`
     colorcube colors (MkV3D 0 2 (-6)) 1
     `mappend`
     colorcube colors (MkV3D 0 0 (-6)) 1

stacked_cubes =
  let colors = [red,green,yellow]
  in rectangle blue (MkV3D 0 (-2) 0) (MkV3D 20 0 0) (MkV3D 0 0 (-40))
     `mappend`
     rectangle blue (MkV3D 0 (4.5) 0) (MkV3D 20 0 0) (MkV3D 0 0 (40))
     `mappend`
     colorcube colors (MkV3D (-2) (-1.5) (-6)) 1
     `mappend`
     colorcube [white] (MkV3D 0 4.2 (-10)) 0.1
     `mappend`
     colorcube [white] (MkV3D 0 3.8 (-10)) 0.1
     `mappend`
     rectangle green (MkV3D (-0.2) 4 (-10))   (MkV3D 0 (-0.5) 0) (MkV3D 0 0 (-0.3))
     `mappend`
     rectangle green (MkV3D (0.2)  4 (-10))   (MkV3D 0 (-0.5) 0) (MkV3D 0 0 0.3)
     `mappend`
     rectangle green (MkV3D 0      4 (-9.8))  (MkV3D 0 0.5    0) (MkV3D 0.3 0 0)
     `mappend`
     rectangle green (MkV3D 0      4 (-10.2)) (MkV3D 0 (-0.5) 0) (MkV3D 0.3 0 0)
     `mappend`
     rectangle orange (MkV3D 2.2 (-0.5) (-10)) (MkV3D 0 12 0) (MkV3D (-5) 0 (-10))
