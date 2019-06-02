/* spaceship
 * Author: Thamashi
 * Creation date: 12/29/2018
 */
MACHINE
    spaceship
    
SEES
    grid
    
SETS
    ALERT_MESSAGES = {SPACESHIP_MOVE_OUT_OF_BOUND,SPACESHIP_HIT_ASTEROID,UNABLE_TO_MOVETO_SAME_LOCATION,SUCCESFULLY_MOVED,DIRECTLY_CANNOT_REACH_STARBASE,WARPDRIVE_SUCCESSFUL,SPACESHIP_DOCKED_SUCCESSFULLY,SAME_POSITION,GAME_STATUS,WON,LOST,START,CONTINUE}

VARIABLES
    curr_location,collision_count,spaceship_route,current_power
    
INVARIANT
    curr_location : (NAT1 * NAT1)
    & curr_location : grid_panel
    & curr_location /: asteroid
    & collision_count : NAT
    & spaceship_route : seq(NAT1 * NAT1)
    & spaceship_route : seq(grid_panel)
    & current_power : NAT
    
INITIALISATION
    current_power,curr_location,collision_count,spaceship_route := 70,home_base,0,[]
    
OPERATIONS
        message <-- move_up = 
        PRE ((curr_location : grid_panel) & (message : ALERT_MESSAGES)& (current_power >= 5) &(curr_location /= starbase))
        THEN 
            IF 
                (prj2(NAT1, NAT1)(curr_location) + 1 > height )
            THEN 
                message := SPACESHIP_MOVE_OUT_OF_BOUND 
            ELSIF 
                ((prj1(NAT1, NAT1)(curr_location), prj2(NAT1, NAT1)                                                (curr_location) ) : asteroid)
            THEN
                current_power := current_power - 10
                || collision_count := collision_count + 1
                || message := SPACESHIP_HIT_ASTEROID
            ELSE
                current_power := current_power - 5
                || curr_location := (prj1(NAT1, NAT1)(curr_location) |-> prj2(NAT1, NAT1)(curr_location) + 1)
                || spaceship_route := spaceship_route <- (prj1(NAT1, NAT1)(curr_location) |-> prj2(NAT1, NAT1)(curr_location)+1)
                || message := SUCCESFULLY_MOVED
            END
        END; 
        
        message <-- move_down = 
        PRE ((curr_location : grid_panel) & (message : ALERT_MESSAGES)& (current_power >= 5) &(curr_location /= starbase))
        THEN 
            IF 
                (prj2(NAT1, NAT1)(curr_location) - 1 <= 0 )
            THEN 
                message := SPACESHIP_MOVE_OUT_OF_BOUND 
            ELSIF 
                ((prj1(NAT1, NAT1)(curr_location), prj2(NAT1, NAT1)                                                (curr_location) ) : asteroid)
            THEN
                current_power := current_power - 10
                || collision_count := collision_count + 1
                || message := SPACESHIP_HIT_ASTEROID
            ELSE
                current_power := current_power - 5
                || curr_location := (prj1(NAT1, NAT1)(curr_location) |-> prj2(NAT1, NAT1)(curr_location) - 1)
                || spaceship_route := spaceship_route <- (prj1(NAT1, NAT1)(curr_location) |-> prj2(NAT1, NAT1)(curr_location) - 1)
                || message := SUCCESFULLY_MOVED
            END
        END;
        
        message <-- move_forward = 
        PRE ((curr_location : grid_panel) & (message : ALERT_MESSAGES)& (current_power >= 5) &(curr_location /= starbase))
        THEN 
            IF 
                (prj1(NAT1, NAT1)(curr_location) + 1 > width )
            THEN 
                message := SPACESHIP_MOVE_OUT_OF_BOUND 
            ELSIF 
                ((prj1(NAT1, NAT1)(curr_location) + 1, prj2(NAT1, NAT1)                                                (curr_location)) : asteroid)
            THEN
                current_power := current_power - 10
                || collision_count := collision_count + 1
                || message := SPACESHIP_HIT_ASTEROID
            ELSE
                current_power := current_power - 5
                || curr_location := (prj1(NAT1, NAT1)(curr_location) + 1 |-> prj2(NAT1, NAT1)(curr_location))
                || spaceship_route := spaceship_route <- (prj1(NAT1, NAT1)(curr_location) + 1 |-> prj2(NAT1, NAT1)(curr_location))
                || message := SUCCESFULLY_MOVED
            END
        END; 
        
        message <-- move_backward = 
        PRE ((curr_location : grid_panel) & (message : ALERT_MESSAGES)& (current_power >= 5) &(curr_location /= starbase))
        THEN 
            IF 
                (prj1(NAT1, NAT1)(curr_location) - 1 <= 0 )
            THEN 
                message := SPACESHIP_MOVE_OUT_OF_BOUND 
            ELSIF 
                ((prj1(NAT1, NAT1)(curr_location) - 1, prj2(NAT1, NAT1)                                                (curr_location) ) : asteroid)
            THEN
                current_power := current_power - 10
                || collision_count := collision_count + 1
                || message := SPACESHIP_HIT_ASTEROID
            ELSE
                current_power := current_power - 5
                || curr_location := (prj1(NAT1, NAT1)(curr_location) - 1|-> prj2(NAT1, NAT1)(curr_location))
                || spaceship_route := spaceship_route <- (prj1(NAT1, NAT1)(curr_location) - 1|-> prj2(NAT1, NAT1)(curr_location))
                || message := SUCCESFULLY_MOVED
            END
        END;
        
        message <-- engageWarpDrive(newposition) = 
        PRE ((curr_location : grid_panel) & (message : ALERT_MESSAGES)& (current_power >= 20) &(curr_location /= starbase) & (newposition : NAT1 * NAT1))
        THEN 
            IF 
                (newposition /: grid_panel )
            THEN 
                message := SPACESHIP_MOVE_OUT_OF_BOUND 
            ELSIF
                (newposition = curr_location )
            THEN 
                message := UNABLE_TO_MOVETO_SAME_LOCATION
            ELSIF 
                (newposition : asteroid)
            THEN
                current_power := current_power - 10
                || collision_count := collision_count + 1
                || message := SPACESHIP_HIT_ASTEROID
            ELSIF
                ((spaceship_route = []) & (newposition = starbase))
            THEN
                message := DIRECTLY_CANNOT_REACH_STARBASE
            ELSE 
                current_power := current_power - 20
                || curr_location := (prj1(NAT1, NAT1)(newposition) |-> prj2(NAT1, NAT1)(newposition))
                || spaceship_route := spaceship_route <- (prj1(NAT1, NAT1)(newposition) |-> prj2(NAT1, NAT1)(newposition))
                || message := WARPDRIVE_SUCCESSFUL
                
               
            END
        END;
        
        message <-- dockedAtStarbase = 
        PRE ((curr_location = starbase) & (message : ALERT_MESSAGES))
        THEN
            message := SPACESHIP_DOCKED_SUCCESSFULLY
        END;
        
        asteroid_collision_count, ship_power, ship_location,message <-- missionStatus = 
        PRE ((curr_location : grid_panel) & (message : ALERT_MESSAGES))
        THEN
            IF
                ((curr_location = home_base) &(current_power =50)& (collision_count = 0) )
            THEN
                message := SAME_POSITION
            ELSE
                ship_location := (prj1(NAT1, NAT1)(curr_location) |-> prj2(NAT1, NAT1)(curr_location))
                || ship_power := curr_location
                || asteroid_collision_count := collision_count
                || message := GAME_STATUS
            END
        END;
        
         message <-- gameStatus = 
         PRE ((curr_location : grid_panel) & (message : ALERT_MESSAGES))
         THEN
          IF
           (curr_location = starbase)
          THEN
           message := WON 
          ELSIF
           ( (current_power =0) & curr_location /= starbase )
          THEN
           message := LOST
          ELSIF
           ((current_power = 50)& (curr_location = home_base))
          THEN
           message := START 
          ELSE
           message := CONTINUE
          END
         END;
         
         mission_route <-- missionRoute = 
         PRE (curr_location : grid_panel)
         THEN
            mission_route := spaceship_route
         END       

END
