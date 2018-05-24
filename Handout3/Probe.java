import java.util.Random;
import java.util.concurrent.*;

/*@

    lemma void cenas();

@*/


class Probe implements Runnable
{

    
    private SensorInt sensor;

    public Probe(SensorInt sensor)
    {
        this.sensor = sensor;
    }


    public void run()
    {
        while( true )
        {
            // produce a new value every 2 seconds
        }
    }
    
    
    private void cenas()
    {
    
    }

}