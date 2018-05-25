import java.util.Random;
import java.util.concurrent.*;

/*@
    predicate ProbeInv(Probe p; int m, int n) =
       p.other |-> ?d &*&
       p.value |-> ?v &*&
       p.sensor |-> ?s &*&
       p.max |-> m &*&
       p.min |-> n &*&
       m > n;
@*/


class Probe implements Runnable
{
   
    //@ predicate pre() = ProbeInv(this, ?m, ?n);
    //@ predicate post() = ProbeInv(this, ?m, ?n);

    int max = 0;
    int min = 0;
    int value = 0;
    
    int other;
    
    SensorInt sensor;
    

    public Probe(SensorInt sensor)
    //@ requires sensor != null;
    //@ ensures post();
    {
        this.sensor = sensor;
        this.max = sensor.getMax();
        this.min = sensor.getMin();
        this.value = r.nextInt(max - min + 1) + min;
    }



    public void run()
    //@ requires ProbeInv(this, ?m, ?n);
    //@ ensures post();
    {
    	
        Random ran = new Random();
    
        while( true )
        //@ invariant ProbeInv(this, m, n);
        {
           // produce a new value every 2 seconds
           value = ran.nextInt(max - min + 1) + min;
           sensor.set(value);
           sleep(2000);
           // Enter in a 2 second sleep, beware of thread sleeps in future
           // Requires change of javaspec to the TimeUnit class (check document)
           
        }
    }

}