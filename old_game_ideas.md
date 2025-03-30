unreal engine has the scaling problem because it is sending every actor channel to every client, but nowadays Epic Games is wanting people to use push model replication / Iris.

I forgot how the squad networking hack works.

like client-side hit registration? with Easy Anticheat.

I forgot all the details

client tells server I fired from this location and velocity, etc. for this projectile/hit trace

server tells everyone if they hit or missed according to what they said

but server is not the authority on the projectiles and never fires them

the other hack on the server was to disable animations completely on the server

there's also a 1-50 meter? hitscan to projectile

some thing about penetration of bullets

Not sure how the vehicle one works. The one for vehicles where the driver seat is the origin for all the other passengers.

Cell based level streaming

Brickworks cell tiles file transfer

Cells loaded to main thread deferred until done.

Mesh streaming by meshlets

Simulate 4000 networked players with frame rate and per connection maximum.